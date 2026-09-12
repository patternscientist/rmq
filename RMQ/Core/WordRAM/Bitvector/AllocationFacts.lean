import RMQ.Core.WordRAM.Bitvector.SelectExperiment

/-!
# Serialized select-directory bit counts

The experiment retains sixteen components from each select directory. Their
serialization has the directory's full payload length minus the four unused
false-rank sample tables. This is a length identity for the actual selected
arrays; differently ordered serialized lists are not identified bit-for-bit.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect Experiment

private theorem flattenPayloadWords_eq_flatten (words : List (List Bool)) :
    flattenPayloadWords words = words.flatten := by
  induction words with
  | nil => rfl
  | cons word words ih => simp [flattenPayloadWords, ih]

/-- The experiment serializes exactly the payload of each selected store. -/
theorem segmentBits_payload {payload : List Bool} (store : PayloadWordStore payload) :
    segmentBits store.words = payload := by
  unfold segmentBits
  rw [← flattenPayloadWords_eq_flatten]
  exact store.payload_eq_words_join

/-- Exact selected bits, in the order used by the experiment's descriptors. -/
theorem directorySegments_bits_eq
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    (directorySegments d).flatMap segmentBits =
      d.superTable.payload ++ d.localTable.payload ++
      d.longFlagRankData.superTables.trueTable.payload ++
      d.longFlagRankData.blockTables.trueTable.payload ++
      d.longFlagBits ++ d.longSuperRelativeTable.payload ++
      d.sparseDirectory.rankData.superTables.trueTable.payload ++
      d.sparseDirectory.rankData.blockTables.trueTable.payload ++
      d.sparseDirectory.flagBits ++ d.sparseDirectory.relativeTable.payload := by
  simp only [directorySegments, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, segmentBits_payload,
    FixedWidthSparseDenseSelectDenseLocalEntryTable.payload, List.append_assoc]

/-- Adding precisely the four omitted sample-table lengths restores full capacity. -/
theorem directorySegments_length_add_omitted
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    ((directorySegments d).flatMap segmentBits).length +
      d.longFlagRankData.superTables.falseTable.payload.length +
      d.longFlagRankData.blockTables.falseTable.payload.length +
      d.sparseDirectory.rankData.superTables.falseTable.payload.length +
      d.sparseDirectory.rankData.blockTables.falseTable.payload.length =
      d.payload.length := by
  rw [directorySegments_bits_eq]
  simp only [SparseExceptionSelectData.payload, SparseExceptionDirectory.payload,
    TwoLevelPayloadLiveStoredWordRankData.auxPayload,
    TwoLevelPayloadLiveStoredWordRankData.superPayload,
    TwoLevelPayloadLiveStoredWordRankData.blockPayload,
    FixedWidthRankSampleTables.payload, List.length_append]
  omega

theorem directorySegments_length_le_payload
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    ((directorySegments d).flatMap segmentBits).length ≤ d.payload.length := by
  have h := directorySegments_length_add_omitted d
  omega

/-- The existing generic directory budget bounds the actual retained arrays. -/
theorem directorySegments_length_le_canonical
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    ((directorySegments d).flatMap segmentBits).length ≤
      canonicalSparseExceptionSelectOverhead bits.length :=
  Nat.le_trans (directorySegments_length_le_payload d) d.payload_length_le_canonical

/-- Both target directories are counted separately, with arbitrary component data. -/
theorem directorySegments_both_length_le
    {bits : List Bool} {rfs rfb rts rtb : Nat}
    (df : SparseExceptionSelectData bits false rfs rfb)
    (dt : SparseExceptionSelectData bits true rts rtb) :
    ((directorySegments df ++ directorySegments dt).flatMap segmentBits).length ≤
      canonicalSparseExceptionSelectOverhead bits.length +
        canonicalSparseExceptionSelectOverhead bits.length := by
  rw [List.flatMap_append, List.length_append]
  exact Nat.add_le_add (directorySegments_length_le_canonical df)
    (directorySegments_length_le_canonical dt)

/-- A positive extra serialized component cannot satisfy the exact same count. -/
theorem directorySegments_positive_extra_breaks_exact_count
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb)
    (extra : List Bool) (hpositive : 0 < extra.length) :
    ¬ (((directorySegments d).flatMap segmentBits ++ extra).length +
      d.longFlagRankData.superTables.falseTable.payload.length +
      d.longFlagRankData.blockTables.falseTable.payload.length +
      d.sparseDirectory.rankData.superTables.falseTable.payload.length +
      d.sparseDirectory.rankData.blockTables.falseTable.payload.length =
      d.payload.length) := by
  have h := directorySegments_length_add_omitted d
  simp only [List.length_append]
  omega

/-- A typed consumer retaining the same selected arrays and directory payload. -/
theorem directoryAllocationFacts
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    (((directorySegments d).flatMap segmentBits).length +
      d.longFlagRankData.superTables.falseTable.payload.length +
      d.longFlagRankData.blockTables.falseTable.payload.length +
      d.sparseDirectory.rankData.superTables.falseTable.payload.length +
      d.sparseDirectory.rankData.blockTables.falseTable.payload.length =
      d.payload.length) ∧
    ((directorySegments d).flatMap segmentBits).length ≤ d.payload.length ∧
    ((directorySegments d).flatMap segmentBits).length ≤
      canonicalSparseExceptionSelectOverhead bits.length :=
  ⟨directorySegments_length_add_omitted d,
    directorySegments_length_le_payload d,
    directorySegments_length_le_canonical d⟩

end RMQ.PackedBitvector

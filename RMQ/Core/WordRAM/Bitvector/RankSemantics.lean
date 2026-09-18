import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram

/-! # Canonical supplied-store rank semantics

The rank view uses the actual Jacobson sample arrays and sentinel-bearing
original raw word array. Only the four actual read segments are constrained.
-/

namespace RMQ.PackedBitvector

open SuccinctRank SuccinctFinal.PackedCellProbe

/-- Logical rank view of the canonical counted components. The raw word view
includes the canonical empty sentinel; its bits are never normalized. -/
def canonicalRankReadStore (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? := fun segment index =>
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    if segment = 17 then (d.superSampleWords target)[index]?
    else if segment = 18 then (d.blockSampleWords target)[index]?
    else if segment = 19 then d.bitWords.store.words[index]?
    else if segment = 21 then (SuccinctClose.bpFringeChunkTable c).store.words[index]?
    else none

/-- Other logical segments may contain the rest of the shared allocation. -/
def RankStoreAgrees (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore) : Prop :=
  ∀ segment index, segment = 17 ∨ segment = 18 ∨ segment = 19 ∨ segment = 21 →
    store.readWord? segment index =
      (canonicalRankReadStore bits target).readWord? segment index

theorem canonical_rank_chunk_geometry (bits : List Bool) :
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    0 < c ∧ d.wordSize ≤ 8 * c := by
  have hmachine : machineWordBits bits.length ≤
      8 * SuccinctClose.bpFringeChunkBits (2 * bits.length) :=
    Nat.le_trans (machineWordBits_mono_le (by omega))
      (SuccinctClose.machineWordBits_le_8_mul_bpFringeChunkBits (2 * bits.length))
  exact ⟨SuccinctClose.bpFringeChunkBits_pos _,
    Nat.le_trans (jacobsonRankData bits).wordSize_le_machine hmachine⟩

/-- Exact supplied-read to chunked-Costed refinement, including the charged
sample, raw word, and chunk-table reads. No semantic oracle supplies the value. -/
theorem rankRead_toCosted_of_agree (bits : List Bool) (target : Bool)
    (store : WordRAM.ReadStore) (hagree : RankStoreAgrees bits target store) (limit : Nat) :
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedRankRead 17 18 19 21 c target store bits.length d.wordSize d.blocksPerSuper limit).toCosted =
      d.bpChunkedRankCosted c target limit := by
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  change (d.bpChunkedRankTraceResultWithStore store 17 18 19 21 c target limit).toCosted = _
  exact d.bpChunkedRankTraceResultWithStore_toCosted_of_agree
    (store := store) (superSegment := 17) (blockSegment := 18)
    (wordSegment := 19) (chunkSegment := 21) (c := c) (target := target)
    (fun i => hagree 17 i (by omega)) (fun i => hagree 18 i (by omega))
    (fun i => hagree 19 i (by omega)) (fun i => hagree 21 i (by omega)) limit

/-- Every limit, including prefixes beyond the input length, returns the
canonical reference rank. All chunk-width hypotheses are derived here. -/
theorem rankRead_value_of_agree (bits : List Bool) (target : Bool)
    (store : WordRAM.ReadStore) (hagree : RankStoreAgrees bits target store) (limit : Nat) :
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedRankRead 17 18 19 21 c target store bits.length d.wordSize d.blocksPerSuper limit).value =
      Succinct.rankPrefix target bits limit := by
  have h := congrArg Costed.value (rankRead_toCosted_of_agree bits target store hagree limit)
  change (packedRankRead 17 18 19 21 (SuccinctClose.bpFringeChunkBits (2 * bits.length))
    target store bits.length (jacobsonRankData bits).wordSize
    (jacobsonRankData bits).blocksPerSuper limit).value =
    ((jacobsonRankData bits).bpChunkedRankCosted
      (SuccinctClose.bpFringeChunkBits (2 * bits.length)) target limit).value at h
  dsimp only
  rw [h]
  obtain ⟨hc, hwidth⟩ := canonical_rank_chunk_geometry bits
  exact (jacobsonRankData bits).bpChunkedRankCosted_exact hc hwidth target limit

theorem canonicalRankRead_value (bits : List Bool) (target : Bool) (limit : Nat) :
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedRankRead 17 18 19 21 c target (canonicalRankReadStore bits target)
      bits.length d.wordSize d.blocksPerSuper limit).value =
      Succinct.rankPrefix target bits limit :=
  rankRead_value_of_agree bits target (canonicalRankReadStore bits target)
    (fun _ _ _ => rfl) limit

-- The consumer pins the four actual read agreements directly to Jacobson's
-- original arrays, without hiding them behind the agreement predicate.
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
    (hsuper : ∀ i, store.readWord? 17 i = ((jacobsonRankData bits).superSampleWords target)[i]?)
    (hblock : ∀ i, store.readWord? 18 i = ((jacobsonRankData bits).blockSampleWords target)[i]?)
    (hword : ∀ i, store.readWord? 19 i = (jacobsonRankData bits).bitWords.store.words[i]?)
    (hchunk : ∀ i, store.readWord? 21 i =
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words[i]?)
    (limit : Nat) :
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedRankRead 17 18 19 21 c target store bits.length d.wordSize d.blocksPerSuper limit).value =
      Succinct.rankPrefix target bits limit := by
  apply rankRead_value_of_agree bits target store _ limit
  intro segment index hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact hsuper index
  · exact hblock index
  · exact hword index
  · exact hchunk index

/-- The same all-input semantic predicate rejects a constant zero answer. -/
theorem constant_zero_rank_rejected :
    ¬ (∀ (bits : List Bool) (target : Bool) (limit : Nat),
      (WordRAM.TraceResult.pure 0).value = Succinct.rankPrefix target bits limit) := by
  intro h
  have hbad := h [true] true 1
  change 0 = 1 at hbad
  cases hbad

end RMQ.PackedBitvector

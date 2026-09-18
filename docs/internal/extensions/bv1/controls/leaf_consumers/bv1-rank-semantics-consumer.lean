import RMQ.Core.WordRAM.Bitvector.RankSemantics
open RMQ RMQ.PackedBitvector RMQ.SuccinctRank RMQ.SuccinctFinal.PackedCellProbe
example (bits : List Bool) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  0 < c ∧ d.wordSize ≤ 8*c := canonical_rank_chunk_geometry bits
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
  (hagree : RankStoreAgrees bits target store) (limit : Nat) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedRankRead 17 18 19 21 c target store bits.length d.wordSize d.blocksPerSuper limit).toCosted =
    d.bpChunkedRankCosted c target limit := rankRead_toCosted_of_agree bits target store hagree limit
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
  (hsuper : ∀ i, store.readWord? 17 i = ((jacobsonRankData bits).superSampleWords target)[i]?)
  (hblock : ∀ i, store.readWord? 18 i = ((jacobsonRankData bits).blockSampleWords target)[i]?)
  (hword : ∀ i, store.readWord? 19 i = (jacobsonRankData bits).bitWords.store.words[i]?)
  (hchunk : ∀ i, store.readWord? 21 i = (SuccinctClose.bpFringeChunkTable
    (SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words[i]?) (limit : Nat) :
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
example (bits : List Bool) (target : Bool) (limit : Nat) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedRankRead 17 18 19 21 c target (canonicalRankReadStore bits target)
    bits.length d.wordSize d.blocksPerSuper limit).value = Succinct.rankPrefix target bits limit :=
  canonicalRankRead_value bits target limit
example (target : Bool) (limit : Nat) :
  (packedRankRead 17 18 19 21 (SuccinctClose.bpFringeChunkBits 0) target
    (canonicalRankReadStore [] target) 0 (jacobsonRankData []).wordSize
    (jacobsonRankData []).blocksPerSuper limit).value = 0 :=
  by simpa only [List.length_nil, Nat.mul_zero, Succinct.rankPrefix_nil] using canonicalRankRead_value [] target limit
example :
  (packedRankRead 17 18 19 21 (SuccinctClose.bpFringeChunkBits 2) true
    (canonicalRankReadStore [true] true) 1 (jacobsonRankData [true]).wordSize
    (jacobsonRankData [true]).blocksPerSuper 10).value = 1 :=
  canonicalRankRead_value [true] true 10
example : ¬ (∀ (bits : List Bool) (target : Bool) (limit : Nat),
  (WordRAM.TraceResult.pure 0).value = Succinct.rankPrefix target bits limit) :=
  constant_zero_rank_rejected
#print axioms canonical_rank_chunk_geometry
#print axioms rankRead_toCosted_of_agree
#print axioms rankRead_value_of_agree
#print axioms canonicalRankRead_value
#print axioms constant_zero_rank_rejected

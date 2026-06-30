import RMQ.Core.RankSelectCompressedSubLogRoute

/-!
# Concrete sub-log compressed/FID payload envelope

This module assembles the payloads that the sub-log local decoder actually
reads:

* the fixed-weight code payload for each sub-log block,
* the narrow length/class tables, and
* the shared decoder table for all possible sub-log fixed-weight blocks.

The result is the first concrete payload constructor for this path: its length
is bounded by the global fixed-weight budget plus `o(n)`, and the access query
is charged through the same stores used in `subLogAccessCosted`.
-/

namespace RMQ

namespace RankSelectSpec

def fixedWeightSubLogConcreteClassLengthPayload
    (bits : List Bool) : List Bool :=
  fixedWeightBlockClassLengthTablePayload (subLogClassWidth bits)
    (fixedWeightSubLogChunkBlocksWithSentinel bits)

def fixedWeightSubLogConcreteAuxPayload
    (bits : List Bool) : List Bool :=
  fixedWeightSubLogConcreteClassLengthPayload bits ++
    fixedWeightSubLogSharedDecoderPayload bits

def fixedWeightSubLogConcretePayload
    (bits : List Bool) : List Bool :=
  fixedWeightBlockCodePayload
      (fixedWeightSubLogChunkBlocksWithSentinel bits) ++
    fixedWeightSubLogConcreteAuxPayload bits

def fixedWeightSubLogConcreteRouteDecoderOverhead : Nat -> Nat :=
  fun n =>
    fixedWeightSubLogChunkBlockCountBoundWithSentinel n +
      (fixedWeightSubLogChunkClassLengthOverhead n +
        fixedWeightSubLogSharedDecoderOverhead
          (fun n => Nat.log2 n + 1) n)

abbrev fixedWeightSubLogConcreteAccessQueryCost : Nat := 4

theorem fixedWeightSubLogConcreteAuxPayload_length_eq
    (bits : List Bool) :
    (fixedWeightSubLogConcreteAuxPayload bits).length =
      fixedWeightBlockClassLengthTableOverhead (subLogClassWidth bits)
          (fixedWeightSubLogChunkBlocksWithSentinel bits) +
        fixedWeightSubLogChunkDenseDecoderBudget bits.length := by
  simp [fixedWeightSubLogConcreteAuxPayload,
    fixedWeightSubLogConcreteClassLengthPayload,
    fixedWeightBlockClassLengthTablePayload_length,
    fixedWeightSubLogSharedDecoderPayload_length_eq]

theorem fixedWeightSubLogConcretePayload_length_eq
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length =
      fixedWeightBlockPayloadBudget
          (fixedWeightSubLogChunkBlocksWithSentinel bits) +
        (fixedWeightBlockClassLengthTableOverhead (subLogClassWidth bits)
            (fixedWeightSubLogChunkBlocksWithSentinel bits) +
          fixedWeightSubLogChunkDenseDecoderBudget bits.length) := by
  simp [fixedWeightSubLogConcretePayload,
    fixedWeightSubLogConcreteAuxPayload_length_eq,
    fixedWeightBlockCodePayload_length]

theorem fixedWeightSubLogConcretePayload_length_le
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length <=
      fixedWeightPayloadBudget bits +
        fixedWeightSubLogConcreteRouteDecoderOverhead bits.length := by
  have hpayload :=
    fixedWeightSubLogConcretePayload_length_eq bits
  have hprimary :=
    fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_bound bits
  have hclass :=
    fixedWeightSubLogChunkBlockClassLengthTableOverhead_le bits
  have hclass' :
      fixedWeightBlockClassLengthTableOverhead (subLogClassWidth bits)
          (fixedWeightSubLogChunkBlocksWithSentinel bits) <=
        fixedWeightSubLogChunkClassLengthOverhead bits.length := by
    simpa [subLogClassWidth] using hclass
  have hdecoder :
      fixedWeightSubLogChunkDenseDecoderBudget bits.length =
        fixedWeightSubLogSharedDecoderOverhead
          (fun n => Nat.log2 n + 1) bits.length := by
    unfold fixedWeightSubLogSharedDecoderOverhead
    rw [fixedWeightSubLogChunkDenseDecoderBudget_eq_rows_mul]
  rw [hpayload]
  rw [hdecoder]
  unfold fixedWeightSubLogConcreteRouteDecoderOverhead
  omega

theorem fixedWeightSubLogConcreteRouteDecoderOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogConcreteRouteDecoderOverhead := by
  have hdecoder :
      SuccinctSpace.LittleOLinear
        (fixedWeightSubLogSharedDecoderOverhead
          (fun n => Nat.log2 n + 1)) :=
    fixedWeightSubLogSharedDecoderOverhead_littleO_of_wordSize_le_log
      (by intro n; omega)
  simpa [fixedWeightSubLogConcreteRouteDecoderOverhead, Nat.add_assoc] using
    fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO.add
      (fixedWeightSubLogChunkClassLengthOverhead_littleO.add hdecoder)

theorem fixedWeightSubLogConcreteCodeStore_word_length_le
    (bits : List Bool) :
    forall {word : List Bool},
      List.Mem word (subLogCodeStore bits).store.words.toList ->
        word.length <= fixedWeightSubLogChunkBlockSize bits.length + 1 :=
  (subLogCodeStore bits).word_length_le

theorem fixedWeightSubLogConcreteLenStore_word_length_le
    (bits : List Bool) :
    forall {word : List Bool},
      List.Mem word (subLogLenStore bits).store.words.toList ->
        word.length <= subLogClassWidth bits :=
  (subLogLenStore bits).word_length_le

theorem fixedWeightSubLogConcreteClassStore_word_length_le
    (bits : List Bool) :
    forall {word : List Bool},
      List.Mem word (subLogClassStore bits).store.words.toList ->
        word.length <= subLogClassWidth bits :=
  (subLogClassStore bits).word_length_le

theorem fixedWeightSubLogConcreteSharedDecoderStore_word_length_le
    (bits : List Bool) :
    forall {word : List Bool},
      List.Mem word
          (fixedWeightSubLogSharedDecoderStore bits).store.words.toList ->
        word.length <= Nat.log2 bits.length + 1 :=
  (fixedWeightSubLogSharedDecoderStore bits).word_length_le

/--
Concrete charged access profile for the sub-log fixed-weight payload
constructor.  This is intentionally access-only: rank/select still require
charged base-rank and select-route directories, not semantic route fields.
-/
theorem fixedWeightSubLogConcreteRouteDecoderAccessProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length <=
        fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcreteRouteDecoderOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcreteRouteDecoderOverhead /\
      (forall i,
        (subLogAccessCosted bits i).cost <=
            fixedWeightSubLogConcreteAccessQueryCost /\
          (subLogAccessCosted bits i).erase = bits[i]?) /\
      (forall {word : List Bool},
        List.Mem word (subLogCodeStore bits).store.words.toList ->
          word.length <= fixedWeightSubLogChunkBlockSize bits.length + 1) /\
      (forall {word : List Bool},
        List.Mem word (subLogLenStore bits).store.words.toList ->
          word.length <= subLogClassWidth bits) /\
      (forall {word : List Bool},
        List.Mem word (subLogClassStore bits).store.words.toList ->
          word.length <= subLogClassWidth bits) /\
      forall {word : List Bool},
        List.Mem word
            (fixedWeightSubLogSharedDecoderStore bits).store.words.toList ->
          word.length <= Nat.log2 bits.length + 1 := by
  refine
    And.intro (fixedWeightSubLogConcretePayload_length_le bits)
      (And.intro fixedWeightSubLogConcreteRouteDecoderOverhead_littleO
        (And.intro ?_
          (And.intro (fixedWeightSubLogConcreteCodeStore_word_length_le bits)
            (And.intro (fixedWeightSubLogConcreteLenStore_word_length_le bits)
              (And.intro
                (fixedWeightSubLogConcreteClassStore_word_length_le bits)
                (fixedWeightSubLogConcreteSharedDecoderStore_word_length_le
                  bits))))))
  intro i
  exact And.intro (by
      rw [subLogAccessCosted_cost]
      change 4 <= 4
      exact Nat.le_refl 4)
    (subLogAccessCosted_erase bits i)

end RankSelectSpec

namespace RankSelect

abbrev subLogAccessCosted :=
  RMQ.RankSelectSpec.subLogAccessCosted

theorem subLogAccessCostedCost (bits : List Bool) (i : Nat) :
    (subLogAccessCosted bits i).cost = 4 := by
  exact RMQ.RankSelectSpec.subLogAccessCosted_cost bits i

theorem subLogAccessCostedErase (bits : List Bool) (i : Nat) :
    (subLogAccessCosted bits i).erase = bits[i]? := by
  exact RMQ.RankSelectSpec.subLogAccessCosted_erase bits i

abbrev subLogRankWithBaseCosted :=
  RMQ.RankSelectSpec.subLogRankWithBaseCosted

theorem subLogRankWithBaseCostedCost
    (bits : List Bool) (target : Bool) (pos baseRank : Nat) :
    (subLogRankWithBaseCosted bits target pos baseRank).cost = 4 := by
  exact
    RMQ.RankSelectSpec.subLogRankWithBaseCosted_cost
      bits target pos baseRank

theorem subLogRankWithBaseCostedEraseOfBase
    (bits : List Bool) (target : Bool) (pos baseRank : Nat)
    (hbase :
      baseRank =
        (RMQ.RankSelectSpec.subLogChunkRankRoute
          bits target pos).baseRank) :
    (subLogRankWithBaseCosted bits target pos baseRank).erase =
      Succinct.rankPrefix target bits pos := by
  exact
    RMQ.RankSelectSpec.subLogRankWithBaseCosted_erase_of_base
      bits target pos baseRank hbase

abbrev subLogSelectWithFieldsCosted :=
  RMQ.RankSelectSpec.subLogSelectWithFieldsCosted

theorem subLogSelectWithFieldsCostedCost
    (bits : List Bool) (target : Bool)
    (fields : RMQ.RankSelectSpec.FixedWeightSubLogClarkSelectRouteFields) :
    (subLogSelectWithFieldsCosted bits target fields).cost = 4 := by
  exact
    RMQ.RankSelectSpec.subLogSelectWithFieldsCosted_cost
      bits target fields

theorem subLogSelectWithFieldsCostedEraseOfExact
    {bits : List Bool} {target : Bool} {occurrence : Nat}
    {fields : RMQ.RankSelectSpec.FixedWeightSubLogClarkSelectRouteFields}
    (hexact :
      exists block,
        (RMQ.RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits)[
            fields.blockIndex]? = some block /\
          (Succinct.select target block fields.localOccurrence).map
              (fun offset => fields.blockStart + offset) =
            Succinct.select target bits occurrence) :
    (subLogSelectWithFieldsCosted bits target fields).erase =
      Succinct.select target bits occurrence := by
  exact
    RMQ.RankSelectSpec.subLogSelectWithFieldsCosted_erase_of_exact hexact

abbrev subLogSelectFromClarkRouteCosted :=
  RMQ.RankSelectSpec.subLogSelectFromClarkRouteCosted

theorem subLogSelectFromClarkRouteCostedCostLe
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromClarkRouteCosted bits target occurrence).cost <=
      GenericSelect.sparseDenseSelectQueryCost + 4 := by
  exact
    RMQ.RankSelectSpec.subLogSelectFromClarkRouteCosted_cost_le
      bits target occurrence

theorem subLogSelectFromClarkRouteCostedErase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromClarkRouteCosted bits target occurrence).erase =
      Succinct.select target bits occurrence := by
  exact
    RMQ.RankSelectSpec.subLogSelectFromClarkRouteCosted_erase
      bits target occurrence

abbrev fixedWeightSubLogConcreteClassLengthPayload :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcreteClassLengthPayload

abbrev fixedWeightSubLogConcreteAuxPayload :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcreteAuxPayload

abbrev fixedWeightSubLogConcretePayload :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcretePayload

abbrev fixedWeightSubLogConcreteRouteDecoderOverhead :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcreteRouteDecoderOverhead

abbrev fixedWeightSubLogConcreteAccessQueryCost :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcreteAccessQueryCost

theorem fixedWeightSubLogConcreteAuxPayloadLengthEq
    (bits : List Bool) :
    (fixedWeightSubLogConcreteAuxPayload bits).length =
      RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead
          (RMQ.RankSelectSpec.subLogClassWidth bits)
          (RMQ.RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits) +
        RMQ.RankSelectSpec.fixedWeightSubLogChunkDenseDecoderBudget
          bits.length := by
  exact RMQ.RankSelectSpec.fixedWeightSubLogConcreteAuxPayload_length_eq bits

theorem fixedWeightSubLogConcretePayloadLengthEq
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length =
      RMQ.RankSelectSpec.fixedWeightBlockPayloadBudget
          (RMQ.RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits) +
        (RMQ.RankSelectSpec.fixedWeightBlockClassLengthTableOverhead
            (RMQ.RankSelectSpec.subLogClassWidth bits)
            (RMQ.RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits) +
          RMQ.RankSelectSpec.fixedWeightSubLogChunkDenseDecoderBudget
            bits.length) := by
  exact RMQ.RankSelectSpec.fixedWeightSubLogConcretePayload_length_eq bits

theorem fixedWeightSubLogConcretePayloadLengthLe
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length <=
      RMQ.RankSelectSpec.fixedWeightPayloadBudget bits +
        fixedWeightSubLogConcreteRouteDecoderOverhead bits.length := by
  exact RMQ.RankSelectSpec.fixedWeightSubLogConcretePayload_length_le bits

theorem fixedWeightSubLogConcreteRouteDecoderOverheadLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogConcreteRouteDecoderOverhead := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcreteRouteDecoderOverhead_littleO

theorem fixedWeightSubLogConcreteRouteDecoderAccessProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length <=
        RMQ.RankSelectSpec.fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcreteRouteDecoderOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcreteRouteDecoderOverhead /\
      (forall i,
        (subLogAccessCosted bits i).cost <=
            fixedWeightSubLogConcreteAccessQueryCost /\
          (subLogAccessCosted bits i).erase = bits[i]?) /\
      (forall {word : List Bool},
        List.Mem word
            (RMQ.RankSelectSpec.subLogCodeStore bits).store.words.toList ->
          word.length <=
            RMQ.RankSelectSpec.fixedWeightSubLogChunkBlockSize bits.length + 1) /\
      (forall {word : List Bool},
        List.Mem word
            (RMQ.RankSelectSpec.subLogLenStore bits).store.words.toList ->
          word.length <= RMQ.RankSelectSpec.subLogClassWidth bits) /\
      (forall {word : List Bool},
        List.Mem word
            (RMQ.RankSelectSpec.subLogClassStore bits).store.words.toList ->
          word.length <= RMQ.RankSelectSpec.subLogClassWidth bits) /\
      forall {word : List Bool},
        List.Mem word
            (RMQ.RankSelectSpec.fixedWeightSubLogSharedDecoderStore bits).store.words.toList ->
          word.length <= Nat.log2 bits.length + 1 := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcreteRouteDecoderAccessProfile bits

end RankSelect

end RMQ

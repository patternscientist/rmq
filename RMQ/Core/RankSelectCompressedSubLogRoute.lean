import RMQ.Core.RankSelectCompressedSubLog
import RMQ.Core.RankSelectTwoLevel

/-!
# Sub-log route-value layer

This module starts the concrete route-directory path for compressed/FID
rank-select.  It pins semantic routes over the sub-log fixed-weight blocks and
then replaces access' local block decode with charged reads from:

* the per-block fixed-weight code payload,
* narrow length/class tables, and
* the shared sub-log decoder table.

Rank/select still need their own charged route envelopes; this file gives the
first payload-backed local kernel that the concrete constructor can consume.
-/

namespace RMQ

namespace RankSelectSpec

def subLogChunkAccessRoute (bits : List Bool) (i : Nat) :
    FixedWeightAmbientComputedRRRAccessRoute bits
      (fixedWeightSubLogChunkBlocksWithSentinel bits) i :=
  fixedWeightChunkAccessRouteWithSentinel
    (fixedWeightSubLogChunkBlockSize_pos bits.length) bits i

def subLogChunkRankRoute (bits : List Bool) (target : Bool) (pos : Nat) :
    FixedWeightAmbientComputedRRRRankRoute bits
      (fixedWeightSubLogChunkBlocksWithSentinel bits) target pos :=
  fixedWeightChunkRankRouteWithSentinel
    (fixedWeightSubLogChunkBlockSize_pos bits.length) bits target pos

def subLogChunkSelectRoute (bits : List Bool) (target : Bool)
    (occurrence : Nat) :
    FixedWeightAmbientComputedRRRSelectRoute bits
      (fixedWeightSubLogChunkBlocksWithSentinel bits) target occurrence :=
  fixedWeightChunkSelectRouteWithSentinel
    (fixedWeightSubLogChunkBlockSize_pos bits.length) bits target occurrence

def subLogDecodeReadCosted (bits : List Bool) (slot : Nat) :
    Costed (Option (List Bool)) :=
  (fixedWeightSubLogSharedDecoderStore bits).store.readWordCosted slot

@[simp] theorem subLogDecodeReadCosted_cost (bits : List Bool) (slot : Nat) :
    (subLogDecodeReadCosted bits slot).cost = 1 := by
  simp [subLogDecodeReadCosted]

theorem subLogDecodeReadCosted_erase_of_block
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    (subLogDecodeReadCosted bits
        (fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block))).erase = some block := by
  simp only [subLogDecodeReadCosted,
    SuccinctSpace.PayloadWordStore.readWordCosted_erase]
  exact fixedWeightSubLogSharedDecoderStore_get?_of_block hblock

def subLogAccessFromDecodeCosted (bits : List Bool) (slot offset : Nat) :
    Costed (Option Bool) :=
  Costed.bind (subLogDecodeReadCosted bits slot) fun decoded? =>
    Costed.pure ((decoded?.getD [])[offset]?)

@[simp] theorem subLogAccessFromDecodeCosted_cost
    (bits : List Bool) (slot offset : Nat) :
    (subLogAccessFromDecodeCosted bits slot offset).cost = 1 := by
  simp [subLogAccessFromDecodeCosted]

theorem subLogAccessFromDecodeCosted_erase_of_block
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block)
    (offset : Nat) :
    (subLogAccessFromDecodeCosted bits
        (fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block)) offset).erase = block[offset]? := by
  simp only [subLogAccessFromDecodeCosted, Costed.erase_bind,
    Costed.erase_pure]
  rw [subLogDecodeReadCosted_erase_of_block hblock]
  simp

def subLogClassWidth (bits : List Bool) : Nat :=
  fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length

def subLogLenStore (bits : List Bool) :
    SuccinctSpace.BoundedPayloadWordStore
      (SuccinctSpace.flattenPayloadWords
        (SuccinctSpace.fixedWidthTableWords (subLogClassWidth bits)
          ((fixedWeightSubLogChunkBlocksWithSentinel bits).map
            (fun block => block.length))))
      (subLogClassWidth bits) :=
  SuccinctSpace.fixedWidthTableStore (subLogClassWidth bits)
    ((fixedWeightSubLogChunkBlocksWithSentinel bits).map
      (fun block => block.length))

def subLogClassStore (bits : List Bool) :
    SuccinctSpace.BoundedPayloadWordStore
      (SuccinctSpace.flattenPayloadWords
        (SuccinctSpace.fixedWidthTableWords (subLogClassWidth bits)
          ((fixedWeightSubLogChunkBlocksWithSentinel bits).map trueCount)))
      (subLogClassWidth bits) :=
  SuccinctSpace.fixedWidthTableStore (subLogClassWidth bits)
    ((fixedWeightSubLogChunkBlocksWithSentinel bits).map trueCount)

theorem subLogLenStore_get?
    {bits : List Bool} {b : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[b]? = some block) :
    (subLogLenStore bits).store.words[b]? =
      some (SuccinctSpace.natToBitsLE (subLogClassWidth bits) block.length) := by
  have hentry :
      ((fixedWeightSubLogChunkBlocksWithSentinel bits).map
          (fun block => block.length))[b]? = some block.length := by
    rw [List.getElem?_map, hblock]
    rfl
  exact SuccinctSpace.fixedWidthTableStore_get? _ _ hentry

theorem subLogClassStore_get?
    {bits : List Bool} {b : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[b]? = some block) :
    (subLogClassStore bits).store.words[b]? =
      some (SuccinctSpace.natToBitsLE
        (subLogClassWidth bits) (trueCount block)) := by
  have hentry :
      ((fixedWeightSubLogChunkBlocksWithSentinel bits).map trueCount)[b]? =
        some (trueCount block) := by
    rw [List.getElem?_map, hblock]
    rfl
  exact SuccinctSpace.fixedWidthTableStore_get? _ _ hentry

theorem subLogBlock_length_lt
    {bits : List Bool} {block : List Bool}
    (hmem : List.Mem block (fixedWeightSubLogChunkBlocksWithSentinel bits)) :
    block.length < 2 ^ subLogClassWidth bits := by
  have h1 : block.length <= fixedWeightSubLogChunkBlockSize bits.length :=
    fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem
  have h2 :
      fixedWeightSubLogChunkBlockSize bits.length <=
        Nat.log2 bits.length + 1 := by
    unfold fixedWeightSubLogChunkBlockSize
    omega
  have h3 : Nat.log2 bits.length + 1 < 2 ^ subLogClassWidth bits := by
    have hw :
        subLogClassWidth bits =
          Nat.log2 (Nat.log2 bits.length + 1) + 1 := rfl
    rw [hw]
    exact Nat.lt_log2_self
  omega

theorem subLogBlock_trueCount_lt
    {bits : List Bool} {block : List Bool}
    (hmem : List.Mem block (fixedWeightSubLogChunkBlocksWithSentinel bits)) :
    trueCount block < 2 ^ subLogClassWidth bits := by
  have hle : trueCount block <= block.length := trueCount_le_length block
  have hlt := subLogBlock_length_lt hmem
  omega

theorem subLogCode_hcode (bits : List Bool) :
    forall {block : List Bool},
      List.Mem block (fixedWeightSubLogChunkBlocksWithSentinel bits) ->
        fixedWeightPayloadBudget block <=
          fixedWeightSubLogChunkBlockSize bits.length + 1 := by
  intro block hmem
  have h1 := fixedWeightPayloadBudget_le_length_add_one block
  have h2 := fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem
  omega

def subLogCodeStore (bits : List Bool) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload
        (fixedWeightSubLogChunkBlocksWithSentinel bits))
      (fixedWeightSubLogChunkBlockSize bits.length + 1) :=
  fixedWeightBlockCodeBoundedStore
    (fixedWeightSubLogChunkBlocksWithSentinel bits) (subLogCode_hcode bits)

theorem subLogCodeStore_get?
    {bits : List Bool} {b : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[b]? = some block) :
    (subLogCodeStore bits).store.words[b]? =
      some (fixedWeightPackedPayload block) :=
  fixedWeightBlockCodeBoundedStore_get?_of_block
    (fixedWeightSubLogChunkBlocksWithSentinel bits)
    (subLogCode_hcode bits) hblock

def subLogAccessCosted (bits : List Bool) (i : Nat) :
    Costed (Option Bool) :=
  Costed.bind
      ((subLogCodeStore bits).store.readWordCosted
        (subLogChunkAccessRoute bits i).blockIndex) fun code? =>
  Costed.bind
      ((subLogLenStore bits).store.readWordCosted
        (subLogChunkAccessRoute bits i).blockIndex) fun len? =>
  Costed.bind
      ((subLogClassStore bits).store.readWordCosted
        (subLogChunkAccessRoute bits i).blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure ((decoded?.getD [])[(subLogChunkAccessRoute bits i).offset]?)

theorem subLogAccessCosted_cost (bits : List Bool) (i : Nat) :
    (subLogAccessCosted bits i).cost = 4 := by
  simp [subLogAccessCosted]

theorem subLogAccessCosted_erase (bits : List Bool) (i : Nat) :
    (subLogAccessCosted bits i).erase = bits[i]? := by
  have hblock := (subLogChunkAccessRoute bits i).block_get
  have hmem :
      List.Mem (subLogChunkAccessRoute bits i).block
        (fixedWeightSubLogChunkBlocksWithSentinel bits) :=
    List.mem_of_getElem? hblock
  have hcode := subLogCodeStore_get? hblock
  have hlen := subLogLenStore_get? hblock
  have hclass := subLogClassStore_get? hblock
  have hlenlt := subLogBlock_length_lt hmem
  have hclasslt := subLogBlock_trueCount_lt hmem
  simp only [subLogAccessCosted, Costed.erase_bind, Costed.erase_pure,
    subLogDecodeReadCosted, SuccinctSpace.PayloadWordStore.readWordCosted_erase]
  rw [hcode, hlen, hclass,
    fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix [] hlenlt hclasslt,
    fixedWeightSubLogSharedDecoderStore_get?_of_block hblock]
  simp only [Option.getD_some]
  exact (subLogChunkAccessRoute bits i).access_exact

def subLogRankFromDecodeCosted
    (bits : List Bool) (target : Bool) (slot localLimit : Nat) :
    Costed Nat :=
  Costed.bind (subLogDecodeReadCosted bits slot) fun decoded? =>
    Costed.pure (Succinct.rankPrefix target (decoded?.getD []) localLimit)

@[simp] theorem subLogRankFromDecodeCosted_cost
    (bits : List Bool) (target : Bool) (slot localLimit : Nat) :
    (subLogRankFromDecodeCosted bits target slot localLimit).cost = 1 := by
  simp [subLogRankFromDecodeCosted]

theorem subLogRankFromDecodeCosted_erase_of_block
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (target : Bool) (localLimit : Nat)
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    (subLogRankFromDecodeCosted bits target
        (fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block)) localLimit).erase =
      Succinct.rankPrefix target block localLimit := by
  simp only [subLogRankFromDecodeCosted, Costed.erase_bind,
    Costed.erase_pure]
  rw [subLogDecodeReadCosted_erase_of_block hblock]
  simp

/--
Rank through the sub-log local decoder, assuming the caller has already
obtained the block's global base rank from charged route metadata.
-/
def subLogRankWithBaseCosted
    (bits : List Bool) (target : Bool) (pos baseRank : Nat) :
    Costed Nat :=
  Costed.bind
      ((subLogCodeStore bits).store.readWordCosted
        (subLogChunkRankRoute bits target pos).blockIndex) fun code? =>
  Costed.bind
      ((subLogLenStore bits).store.readWordCosted
        (subLogChunkRankRoute bits target pos).blockIndex) fun len? =>
  Costed.bind
      ((subLogClassStore bits).store.readWordCosted
        (subLogChunkRankRoute bits target pos).blockIndex) fun class? =>
  Costed.bind
      (subLogDecodeReadCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure
      (baseRank +
        Succinct.rankPrefix target
          (decoded?.getD []) (subLogChunkRankRoute bits target pos).localLimit)

theorem subLogRankWithBaseCosted_cost
    (bits : List Bool) (target : Bool) (pos baseRank : Nat) :
    (subLogRankWithBaseCosted bits target pos baseRank).cost = 4 := by
  simp [subLogRankWithBaseCosted]

theorem subLogRankWithBaseCosted_erase_of_base
    (bits : List Bool) (target : Bool) (pos baseRank : Nat)
    (hbase : baseRank = (subLogChunkRankRoute bits target pos).baseRank) :
    (subLogRankWithBaseCosted bits target pos baseRank).erase =
      Succinct.rankPrefix target bits pos := by
  let route := subLogChunkRankRoute bits target pos
  have hblock := route.block_get
  have hmem :
      List.Mem route.block
        (fixedWeightSubLogChunkBlocksWithSentinel bits) :=
    List.mem_of_getElem? hblock
  have hcode := subLogCodeStore_get? hblock
  have hlen := subLogLenStore_get? hblock
  have hclass := subLogClassStore_get? hblock
  have hlenlt := subLogBlock_length_lt hmem
  have hclasslt := subLogBlock_trueCount_lt hmem
  simp only [subLogRankWithBaseCosted, Costed.erase_bind, Costed.erase_pure,
    subLogDecodeReadCosted, SuccinctSpace.PayloadWordStore.readWordCosted_erase]
  rw [hcode, hlen, hclass,
    fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix [] hlenlt hclasslt,
    fixedWeightSubLogSharedDecoderStore_get?_of_block hblock]
  simp only [Option.getD_some]
  rw [hbase]
  exact route.rank_exact

/--
Select through the sub-log local decoder, assuming the caller has already
obtained final Clark route fields from charged route metadata.
-/
def subLogSelectWithFieldsCosted
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    Costed (Option Nat) :=
  Costed.bind
      ((subLogCodeStore bits).store.readWordCosted fields.blockIndex)
      fun code? =>
  Costed.bind
      ((subLogLenStore bits).store.readWordCosted fields.blockIndex)
      fun len? =>
  Costed.bind
      ((subLogClassStore bits).store.readWordCosted fields.blockIndex)
      fun class? =>
  Costed.bind
      (subLogDecodeReadCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure
      ((Succinct.select target
          (decoded?.getD []) fields.localOccurrence).map
        (fun offset => fields.blockStart + offset))

theorem subLogSelectWithFieldsCosted_cost
    (bits : List Bool) (target : Bool)
    (fields : FixedWeightSubLogClarkSelectRouteFields) :
    (subLogSelectWithFieldsCosted bits target fields).cost = 4 := by
  simp [subLogSelectWithFieldsCosted]

theorem subLogSelectWithFieldsCosted_erase_of_exact
    {bits : List Bool} {target : Bool} {occurrence : Nat}
    {fields : FixedWeightSubLogClarkSelectRouteFields}
    (hexact :
      exists block,
        (fixedWeightSubLogChunkBlocksWithSentinel bits)[
            fields.blockIndex]? = some block /\
          (Succinct.select target block fields.localOccurrence).map
              (fun offset => fields.blockStart + offset) =
            Succinct.select target bits occurrence) :
    (subLogSelectWithFieldsCosted bits target fields).erase =
      Succinct.select target bits occurrence := by
  cases hexact with
  | intro block hrest =>
      cases hrest with
      | intro hblock hselect =>
          have hmem :
              List.Mem block
                (fixedWeightSubLogChunkBlocksWithSentinel bits) :=
            List.mem_of_getElem? hblock
          have hcode := subLogCodeStore_get? hblock
          have hlen := subLogLenStore_get? hblock
          have hclass := subLogClassStore_get? hblock
          have hlenlt := subLogBlock_length_lt hmem
          have hclasslt := subLogBlock_trueCount_lt hmem
          simp only [subLogSelectWithFieldsCosted, Costed.erase_bind,
            Costed.erase_pure, subLogDecodeReadCosted,
            SuccinctSpace.PayloadWordStore.readWordCosted_erase]
          rw [hcode, hlen, hclass,
            fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix []
              hlenlt hclasslt,
            fixedWeightSubLogSharedDecoderStore_get?_of_block hblock]
          simp only [Option.getD_some]
          exact hselect

/--
Select through the current Clark route source and the concrete sub-log local
decoder.  This consumes the route-field exactness theorem, but the route source
still carries its documented raw dense bit-word reads.
-/
def subLogSelectFromClarkRouteCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    (fixedWeightSubLogClarkSelectRouteFieldsCosted bits target occurrence)
    fun fields? =>
      match fields? with
      | none => Costed.pure none
      | some fields => subLogSelectWithFieldsCosted bits target fields

theorem subLogSelectFromClarkRouteCosted_cost_le
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromClarkRouteCosted bits target occurrence).cost <=
      GenericSelect.sparseDenseSelectQueryCost + 4 := by
  have hroute :=
    fixedWeightSubLogClarkSelectRouteFieldsCosted_cost_le
      bits target occurrence
  unfold subLogSelectFromClarkRouteCosted
  rw [Costed.cost_bind]
  cases hfields :
      (fixedWeightSubLogClarkSelectRouteFieldsCosted
        bits target occurrence).erase with
  | none =>
      simp [Costed.erase] at hfields
      simp [hfields]
      omega
  | some fields =>
      simp [Costed.erase] at hfields
      simp [hfields, subLogSelectWithFieldsCosted_cost bits target fields]
      omega

theorem subLogSelectFromClarkRouteCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (subLogSelectFromClarkRouteCosted bits target occurrence).erase =
      Succinct.select target bits occurrence := by
  have herase :=
    fixedWeightSubLogClarkSelectRouteFieldsCosted_erase
      bits target occurrence
  unfold subLogSelectFromClarkRouteCosted
  simp only [Costed.erase_bind]
  cases hfields :
      (fixedWeightSubLogClarkSelectRouteFieldsCosted
        bits target occurrence).erase with
  | none =>
      rw [hfields] at herase
      cases hselect : Succinct.select target bits occurrence with
      | none =>
          simp
      | some idx =>
          simp [hselect] at herase
  | some fields =>
      simpa using subLogSelectWithFieldsCosted_erase_of_exact
        (fixedWeightSubLogClarkSelectRouteFieldsCosted_select_exact
          hfields)

end RankSelectSpec

end RMQ

import RMQ.Core.RankSelectCompressedSubLogDirectory

/-!
# Sub-log select-route payload layer

This owned leaf records the strongest select-route progress available without
changing the existing Clark source.  The positive theorem is deliberately
local: once a select route has produced final
`FixedWeightSubLogClarkSelectRouteFields`, the selected offset is recovered
through the packed fixed-weight code store, length/class stores, and the shared
sub-log decoder.  No raw dense bit word is read by this field consumer.

The obstruction theorem below names the remaining Clark-replacement trap:
trying to make the final route-field table direct-occurrence indexed forces a
linear route payload on dense false bitvectors.
-/

namespace RMQ

namespace RankSelectSpec

/-- The packed stores read by the final sub-log select-field consumer. -/
def fixedWeightSubLogSelectPackedLocalReadWords
    (bits : List Bool) : List (List Bool) :=
  (((subLogCodeStore bits).store.words.toList ++
      (subLogLenStore bits).store.words.toList) ++
    (subLogClassStore bits).store.words.toList) ++
      (fixedWeightSubLogSharedDecoderStore bits).store.words.toList

/--
Every word read by the final select-field consumer comes from one of the
packed-code, length/class, or shared-decoder stores.  The disjunction records
the native width bound for the store it came from.
-/
theorem fixedWeightSubLogSelectPackedLocalReadWords_widths
    (bits : List Bool) :
    forall {word : List Bool},
      List.Mem word
          (fixedWeightSubLogSelectPackedLocalReadWords bits) ->
        word.length <= fixedWeightSubLogChunkBlockSize bits.length + 1 \/
          word.length <= subLogClassWidth bits \/
          word.length <= Nat.log2 bits.length + 1 := by
  intro word hmem
  unfold fixedWeightSubLogSelectPackedLocalReadWords at hmem
  rcases List.mem_append.mp hmem with hprefix | hdecoder
  · rcases List.mem_append.mp hprefix with hprefix | hclass
    · rcases List.mem_append.mp hprefix with hcode | hlen
      · exact Or.inl
          (fixedWeightSubLogConcreteCodeStore_word_length_le bits hcode)
      · exact Or.inr (Or.inl
          (fixedWeightSubLogConcreteLenStore_word_length_le bits hlen))
    · exact Or.inr (Or.inl
        (fixedWeightSubLogConcreteClassStore_word_length_le bits hclass))
  · exact Or.inr (Or.inr
      (fixedWeightSubLogConcreteSharedDecoderStore_word_length_le
        bits hdecoder))

/--
Concrete packed local select-field profile.

This does not claim to replace the Clark route source.  It says that after a
route source supplies exact final fields, the remaining select computation is
charged entirely to the existing packed-code/class/shared-decoder stores.
-/
theorem fixedWeightSubLogSelectPackedLocalDecoderProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcretePayload bits).length <=
        fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcreteRouteDecoderOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcreteRouteDecoderOverhead /\
      (forall target
          (fields : FixedWeightSubLogClarkSelectRouteFields),
        (subLogSelectWithFieldsCosted bits target fields).cost = 4) /\
      (forall target occurrence
          (fields : FixedWeightSubLogClarkSelectRouteFields),
        (exists block,
          (fixedWeightSubLogChunkBlocksWithSentinel bits)[
              fields.blockIndex]? = some block /\
            (Succinct.select target block fields.localOccurrence).map
                (fun offset => fields.blockStart + offset) =
              Succinct.select target bits occurrence) ->
          (subLogSelectWithFieldsCosted bits target fields).erase =
            Succinct.select target bits occurrence) /\
      forall {word : List Bool},
        List.Mem word
            (fixedWeightSubLogSelectPackedLocalReadWords bits) ->
          word.length <= fixedWeightSubLogChunkBlockSize bits.length + 1 \/
            word.length <= subLogClassWidth bits \/
            word.length <= Nat.log2 bits.length + 1 := by
  exact
    ⟨fixedWeightSubLogConcretePayload_length_le bits,
      fixedWeightSubLogConcreteRouteDecoderOverhead_littleO,
      (fun target fields =>
        subLogSelectWithFieldsCosted_cost bits target fields),
      (fun target occurrence fields hexact =>
        subLogSelectWithFieldsCosted_erase_of_exact hexact),
      fixedWeightSubLogSelectPackedLocalReadWords_widths bits⟩

/--
If a final route-field table reuses the same three select-field slots for two
queries, it cannot distinguish their semantic select answers.

This is the local obstruction to replacing Clark's route evaluator with only a
coalesced table of final `(blockIndex, localOccurrence, blockStart)` fields.
-/
theorem fixedWeightSubLogSelectRouteSameFinalFieldSlotsSelectEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {occurrenceA occurrenceB : Nat}
    (hblock :
      data.selectBlockLocalSlot target occurrenceA =
        data.selectBlockLocalSlot target occurrenceB)
    (hlocal :
      data.selectLocalOccurrenceLocalSlot target occurrenceA =
        data.selectLocalOccurrenceLocalSlot target occurrenceB)
    (hstart :
      data.selectBlockStartLocalSlot target occurrenceA =
        data.selectBlockStartLocalSlot target occurrenceB) :
    Succinct.select target bits occurrenceA =
      Succinct.select target bits occurrenceB := by
  exact
    fixedWeightRouteFieldTableLayout_sameSelectSlots_select_eq
      data hblock hlocal hstart

/--
Direct occurrence-indexed final select-route fields cannot be the sublinear
compressed/FID select-route replacement: on `List.replicate n false`, slot
`k -> k` forces at least `n` route-payload bits, contradicting the existing
fixed-slot `o(n)` route-field-table family budget.
-/
theorem no_fixedWeightSubLogSelectRouteDirectOccurrenceSlots
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hfield :
      forall n : Nat,
        0 <
          (family.componentData (List.replicate n false)).fieldWidth)
    (hdirect :
      forall n occurrence : Nat,
        occurrence < n ->
          (family.componentData
              (List.replicate n false)).selectBlockLocalSlot
            false occurrence = occurrence) :
    False := by
  exact
    no_fixedWeightRouteFieldTableLayoutFamily_directSelectOccurrenceSlots
      family hfield hdirect

end RankSelectSpec

namespace RankSelect

abbrev fixedWeightSubLogSelectPackedLocalReadWords :=
  RMQ.RankSelectSpec.fixedWeightSubLogSelectPackedLocalReadWords

theorem fixedWeightSubLogSelectPackedLocalDecoderProfile
    (bits : List Bool) :
    (RMQ.RankSelectSpec.fixedWeightSubLogConcretePayload bits).length <=
        RMQ.RankSelectSpec.fixedWeightPayloadBudget bits +
          RMQ.RankSelectSpec.fixedWeightSubLogConcreteRouteDecoderOverhead
            bits.length /\
      SuccinctSpace.LittleOLinear
        RMQ.RankSelectSpec.fixedWeightSubLogConcreteRouteDecoderOverhead /\
      (forall target
          (fields : RMQ.RankSelectSpec.FixedWeightSubLogClarkSelectRouteFields),
        (RMQ.RankSelectSpec.subLogSelectWithFieldsCosted
          bits target fields).cost = 4) /\
      (forall target occurrence
          (fields : RMQ.RankSelectSpec.FixedWeightSubLogClarkSelectRouteFields),
        (exists block,
          (RMQ.RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits)[
              fields.blockIndex]? = some block /\
            (Succinct.select target block fields.localOccurrence).map
                (fun offset => fields.blockStart + offset) =
              Succinct.select target bits occurrence) ->
          (RMQ.RankSelectSpec.subLogSelectWithFieldsCosted
            bits target fields).erase =
            Succinct.select target bits occurrence) /\
      forall {word : List Bool},
        List.Mem word
            (fixedWeightSubLogSelectPackedLocalReadWords bits) ->
          word.length <=
              RMQ.RankSelectSpec.fixedWeightSubLogChunkBlockSize
                bits.length + 1 \/
            word.length <= RMQ.RankSelectSpec.subLogClassWidth bits \/
            word.length <= Nat.log2 bits.length + 1 := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogSelectPackedLocalDecoderProfile bits

theorem fixedWeightSubLogSelectRouteSameFinalFieldSlotsSelectEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {occurrenceA occurrenceB : Nat}
    (hblock :
      data.selectBlockLocalSlot target occurrenceA =
        data.selectBlockLocalSlot target occurrenceB)
    (hlocal :
      data.selectLocalOccurrenceLocalSlot target occurrenceA =
        data.selectLocalOccurrenceLocalSlot target occurrenceB)
    (hstart :
      data.selectBlockStartLocalSlot target occurrenceA =
        data.selectBlockStartLocalSlot target occurrenceB) :
    Succinct.select target bits occurrenceA =
      Succinct.select target bits occurrenceB := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogSelectRouteSameFinalFieldSlotsSelectEq
      data hblock hlocal hstart

theorem noFixedWeightSubLogSelectRouteDirectOccurrenceSlots
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      RMQ.RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hfield :
      forall n : Nat,
        0 <
          (family.componentData (List.replicate n false)).fieldWidth)
    (hdirect :
      forall n occurrence : Nat,
        occurrence < n ->
          (family.componentData
              (List.replicate n false)).selectBlockLocalSlot
            false occurrence = occurrence) :
    False := by
  exact
    RMQ.RankSelectSpec.no_fixedWeightSubLogSelectRouteDirectOccurrenceSlots
      family hfield hdirect

end RankSelect

end RMQ

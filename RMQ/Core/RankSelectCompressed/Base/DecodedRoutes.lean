import RMQ.Core.RankSelectCompressed.Base.Core

namespace RMQ

namespace RankSelectSpec

/--
Decoded access route fields recovered from charged route metadata.

The semantic block witness remains in
`FixedWeightAmbientComputedRRRAccessRoute`; this record names the runtime route
fields that a concrete table decoder must produce from payload reads.
-/
structure FixedWeightAmbientComputedRRRDecodedAccessRoute where
  blockIndex : Nat
  offset : Nat

/-- Decoded rank route fields recovered from charged route metadata. -/
structure FixedWeightAmbientComputedRRRDecodedRankRoute where
  blockIndex : Nat
  localLimit : Nat
  baseRank : Nat

/-- Decoded select route fields recovered from charged route metadata. -/
structure FixedWeightAmbientComputedRRRDecodedSelectRoute where
  blockIndex : Nat
  localOccurrence : Nat
  blockStart : Nat

def fixedWeightAmbientComputedRRRAccessRouteDecoded
    {bits : List Bool} {blocks : List (List Bool)} {i : Nat}
    (route : FixedWeightAmbientComputedRRRAccessRoute bits blocks i) :
    FixedWeightAmbientComputedRRRDecodedAccessRoute where
  blockIndex := route.blockIndex
  offset := route.offset

def fixedWeightAmbientComputedRRRRankRouteDecoded
    {bits : List Bool} {blocks : List (List Bool)}
    {target : Bool} {pos : Nat}
    (route :
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos) :
    FixedWeightAmbientComputedRRRDecodedRankRoute where
  blockIndex := route.blockIndex
  localLimit := route.localLimit
  baseRank := route.baseRank

def fixedWeightAmbientComputedRRRSelectRouteDecoded
    {bits : List Bool} {blocks : List (List Bool)}
    {target : Bool} {occurrence : Nat}
    (route :
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence) :
    FixedWeightAmbientComputedRRRDecodedSelectRoute where
  blockIndex := route.blockIndex
  localOccurrence := route.localOccurrence
  blockStart := route.blockStart

/--
Route/class table data whose runtime route fields are decoded from charged
metadata reads.

This strengthens `FixedWeightAmbientComputedRRRRouteTableData` without changing
its ambient consumer: the read schedules are explicit functions of the query,
the charged route-store words are read through bounded-store kernels, and the
decoder exactness fields connect those read values to the block index and
local route parameters consumed by the ambient computed-RRR evaluator.
-/
structure FixedWeightAmbientComputedRRRDecodedRouteTableData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  blockSize : Nat
  blockSize_pos : 0 < blockSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_length_le :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length <= blockSize
  blockSize_le_wordSize : blockSize <= wordSize
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  codeStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize
  codeStore_aligned :
    codeStore.store.words.toList = fixedWeightBlockCodeWords blocks
  routePayload : List Bool
  routeStore :
    SuccinctSpace.BoundedPayloadWordStore routePayload wordSize
  routePayload_length_eq : routePayload.length = overhead
  accessMetadataReads : Nat -> List Nat
  rankMetadataReads : Bool -> Nat -> List Nat
  selectMetadataReads : Bool -> Nat -> List Nat
  accessRouteDecoder :
    Nat -> List (Option (List Bool)) ->
      FixedWeightAmbientComputedRRRDecodedAccessRoute
  rankRouteDecoder :
    Bool -> Nat -> List (Option (List Bool)) ->
      FixedWeightAmbientComputedRRRDecodedRankRoute
  selectRouteDecoder :
    Bool -> Nat -> List (Option (List Bool)) ->
      FixedWeightAmbientComputedRRRDecodedSelectRoute
  accessRoute :
    forall i,
      FixedWeightAmbientComputedRRRAccessRoute bits blocks i
  rankRoute :
    forall target pos,
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos
  selectRoute :
    forall target occurrence,
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence
  access_metadata_reads_le :
    forall i, (accessMetadataReads i).length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankMetadataReads target pos).length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectMetadataReads target occurrence).length <= routeCost
  access_route_metadata_reads_eq :
    forall i, (accessRoute i).metadataReads = accessMetadataReads i
  rank_route_metadata_reads_eq :
    forall target pos,
      (rankRoute target pos).metadataReads = rankMetadataReads target pos
  select_route_metadata_reads_eq :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads =
        selectMetadataReads target occurrence
  access_route_decode_exact :
    forall i,
      accessRouteDecoder i
          (boundedPayloadWordReadValues routeStore
            (accessMetadataReads i)) =
        fixedWeightAmbientComputedRRRAccessRouteDecoded (accessRoute i)
  rank_route_decode_exact :
    forall target pos,
      rankRouteDecoder target pos
          (boundedPayloadWordReadValues routeStore
            (rankMetadataReads target pos)) =
        fixedWeightAmbientComputedRRRRankRouteDecoded
          (rankRoute target pos)
  select_route_decode_exact :
    forall target occurrence,
      selectRouteDecoder target occurrence
          (boundedPayloadWordReadValues routeStore
            (selectMetadataReads target occurrence)) =
        fixedWeightAmbientComputedRRRSelectRouteDecoded
          (selectRoute target occurrence)
  local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost
  route_plus_local_le : routeCost + localQueryCost <= queryCost

namespace FixedWeightAmbientComputedRRRDecodedRouteTableData

def toRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  blockSize := data.blockSize
  blockSize_pos := data.blockSize_pos
  blocks_flatten := data.blocks_flatten
  block_length_le := data.block_length_le
  blockSize_le_wordSize := data.blockSize_le_wordSize
  block_code_width_le := data.block_code_width_le
  codeStore := data.codeStore
  codeStore_aligned := data.codeStore_aligned
  routePayload := data.routePayload
  routeStore := data.routeStore
  routePayload_length_eq := data.routePayload_length_eq
  accessRoute := data.accessRoute
  rankRoute := data.rankRoute
  selectRoute := data.selectRoute
  access_metadata_reads_le := by
    intro i
    rw [data.access_route_metadata_reads_eq i]
    exact data.access_metadata_reads_le i
  rank_metadata_reads_le := by
    intro target pos
    rw [data.rank_route_metadata_reads_eq target pos]
    exact data.rank_metadata_reads_le target pos
  select_metadata_reads_le := by
    intro target occurrence
    rw [data.select_route_metadata_reads_eq target occurrence]
    exact data.select_metadata_reads_le target occurrence
  local_query_cost_le := data.local_query_cost_le
  route_plus_local_le := data.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toRouteTableData.toAmbientBlockCompositionData

def accessMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.accessMetadataReads i)

def rankMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.rankMetadataReads target pos)

def selectMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.selectMetadataReads target occurrence)

def DecodedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toRouteTableData.RouteTableProfile /\
    data.routePayload.length = overhead /\
    SuccinctSpace.flattenPayloadWords data.routeStore.store.words.toList =
      data.routePayload /\
    (forall {word : List Bool},
      List.Mem word data.routeStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      (data.accessMetadataReadsCosted i).cost <= routeCost /\
        (data.accessMetadataReadsCosted i).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.accessMetadataReads i) /\
        data.accessRouteDecoder i
            (data.accessMetadataReadsCosted i).erase =
          fixedWeightAmbientComputedRRRAccessRouteDecoded
            (data.accessRoute i) /\
        (data.accessRoute i).metadataReads =
          data.accessMetadataReads i) /\
    (forall target pos,
      (data.rankMetadataReadsCosted target pos).cost <= routeCost /\
        (data.rankMetadataReadsCosted target pos).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.rankMetadataReads target pos) /\
        data.rankRouteDecoder target pos
            (data.rankMetadataReadsCosted target pos).erase =
          fixedWeightAmbientComputedRRRRankRouteDecoded
            (data.rankRoute target pos) /\
        (data.rankRoute target pos).metadataReads =
          data.rankMetadataReads target pos) /\
    (forall target occurrence,
      (data.selectMetadataReadsCosted target occurrence).cost <=
          routeCost /\
        (data.selectMetadataReadsCosted target occurrence).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.selectMetadataReads target occurrence) /\
        data.selectRouteDecoder target occurrence
            (data.selectMetadataReadsCosted target occurrence).erase =
          fixedWeightAmbientComputedRRRSelectRouteDecoded
            (data.selectRoute target occurrence) /\
        (data.selectRoute target occurrence).metadataReads =
          data.selectMetadataReads target occurrence) /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost) /\
    routeCost + localQueryCost <= queryCost

def DecodedMetadataReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  (forall i,
    (Costed.map (data.accessRouteDecoder i)
        (data.accessMetadataReadsCosted i)).cost <= routeCost /\
      (Costed.map (data.accessRouteDecoder i)
        (data.accessMetadataReadsCosted i)).erase =
        fixedWeightAmbientComputedRRRAccessRouteDecoded
          (data.accessRoute i)) /\
    (forall target pos,
      (Costed.map (data.rankRouteDecoder target pos)
          (data.rankMetadataReadsCosted target pos)).cost <=
          routeCost /\
        (Costed.map (data.rankRouteDecoder target pos)
          (data.rankMetadataReadsCosted target pos)).erase =
          fixedWeightAmbientComputedRRRRankRouteDecoded
            (data.rankRoute target pos)) /\
    (forall target occurrence,
      (Costed.map (data.selectRouteDecoder target occurrence)
          (data.selectMetadataReadsCosted target occurrence)).cost <=
          routeCost /\
        (Costed.map (data.selectRouteDecoder target occurrence)
          (data.selectMetadataReadsCosted target occurrence)).erase =
          fixedWeightAmbientComputedRRRSelectRouteDecoded
            (data.selectRoute target occurrence))

theorem decoded_metadata_read_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.DecodedMetadataReadProfile := by
  exact
    ⟨(fun i => by
        constructor
        · dsimp [accessMetadataReadsCosted]
          simpa using data.access_metadata_reads_le i
        · simp [accessMetadataReadsCosted,
            data.access_route_decode_exact i]),
      (fun target pos => by
        constructor
        · dsimp [rankMetadataReadsCosted]
          simpa using data.rank_metadata_reads_le target pos
        · simp [rankMetadataReadsCosted,
            data.rank_route_decode_exact target pos]),
      (fun target occurrence => by
        constructor
        · dsimp [selectMetadataReadsCosted]
          simpa using data.select_metadata_reads_le target occurrence
        · simp [selectMetadataReadsCosted,
            data.select_route_decode_exact target occurrence])⟩

theorem decoded_route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.DecodedRouteTableProfile := by
  exact
    ⟨data.toRouteTableData.route_table_profile,
      data.routePayload_length_eq,
      data.routeStore.erases,
      (fun hmem => data.routeStore.word_length_le_of_mem hmem),
      (fun i => by
        exact
          ⟨by
            dsimp [accessMetadataReadsCosted]
            simpa using data.access_metadata_reads_le i,
            by simp [accessMetadataReadsCosted],
            by
              simpa [accessMetadataReadsCosted] using
                data.access_route_decode_exact i,
            data.access_route_metadata_reads_eq i⟩),
      (fun target pos => by
        exact
          ⟨by
            dsimp [rankMetadataReadsCosted]
            simpa using data.rank_metadata_reads_le target pos,
            by simp [rankMetadataReadsCosted],
            by
              simpa [rankMetadataReadsCosted] using
                data.rank_route_decode_exact target pos,
            data.rank_route_metadata_reads_eq target pos⟩),
      (fun target occurrence => by
        exact
          ⟨by
            dsimp [selectMetadataReadsCosted]
            simpa using data.select_metadata_reads_le
              target occurrence,
            by simp [selectMetadataReadsCosted],
            by
              simpa [selectMetadataReadsCosted] using
                data.select_route_decode_exact target occurrence,
            data.select_route_metadata_reads_eq target occurrence⟩),
      data.local_query_cost_le,
      data.route_plus_local_le⟩

end FixedWeightAmbientComputedRRRDecodedRouteTableData

/--
Family of decoded route/class metadata tables for ambient computed-RRR blocks.

This is the stricter route-table predecessor: it retains the same ambient
block-composition directory but additionally proves that route fields are
outputs of fixed decoders over charged metadata words.
-/
structure FixedWeightAmbientComputedRRRDecodedRouteTableFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRDecodedRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRDecodedRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toAmbientBlockCompositionData

def toAmbientBlockCompositionFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionFamily slots queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := family.directory bits

theorem decoded_route_table_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.DecodedRouteTableProfile /\
          data.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    exact
      ⟨data.decoded_route_table_profile,
        data.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        (family.componentData bits).DecodedRouteTableProfile /\
          let data := family.directory bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                compressedOverhead slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientBlockCompositionFamily.word_bounded_compressed_profile_of_primary_budget
      family.toAmbientBlockCompositionFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead] using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).decoded_route_table_profile
    · simpa [directory, toAmbientBlockCompositionFamily, componentData,
        compressedOverhead] using hcompressed.2 bits

end FixedWeightAmbientComputedRRRDecodedRouteTableFamily

/-- Decode one fixed-width route metadata word read. -/
def fixedWeightRouteNatFromReadValue : Option (List Bool) -> Nat
  | some word => SuccinctSpace.bitsToNatLE word
  | none => 0

/-- Access-route decoder over two charged metadata words. -/
def fixedWeightPackedRouteAccessDecoder
    (readWords : List (Option (List Bool))) :
    FixedWeightAmbientComputedRRRDecodedAccessRoute :=
  match readWords with
  | block? :: offset? :: _ =>
      { blockIndex := fixedWeightRouteNatFromReadValue block?
        offset := fixedWeightRouteNatFromReadValue offset? }
  | _ => { blockIndex := 0, offset := 0 }

/-- Rank-route decoder over three charged metadata words. -/
def fixedWeightPackedRouteRankDecoder
    (readWords : List (Option (List Bool))) :
    FixedWeightAmbientComputedRRRDecodedRankRoute :=
  match readWords with
  | block? :: localLimit? :: baseRank? :: _ =>
      { blockIndex := fixedWeightRouteNatFromReadValue block?
        localLimit := fixedWeightRouteNatFromReadValue localLimit?
        baseRank := fixedWeightRouteNatFromReadValue baseRank? }
  | _ =>
      { blockIndex := 0, localLimit := 0, baseRank := 0 }

/-- Select-route decoder over three charged metadata words. -/
def fixedWeightPackedRouteSelectDecoder
    (readWords : List (Option (List Bool))) :
    FixedWeightAmbientComputedRRRDecodedSelectRoute :=
  match readWords with
  | block? :: localOccurrence? :: blockStart? :: _ =>
      { blockIndex := fixedWeightRouteNatFromReadValue block?
        localOccurrence :=
          fixedWeightRouteNatFromReadValue localOccurrence?
        blockStart := fixedWeightRouteNatFromReadValue blockStart? }
  | _ =>
      { blockIndex := 0, localOccurrence := 0, blockStart := 0 }

@[simp] theorem fixedWeightRouteNatFromReadValue_encoded
    {fieldWidth value : Nat} (hvalue : value < 2 ^ fieldWidth) :
    fixedWeightRouteNatFromReadValue
        (some (SuccinctSpace.natToBitsLE fieldWidth value)) =
      value := by
  simp [fixedWeightRouteNatFromReadValue,
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hvalue]

/--
Packed fixed-width route metadata words for ambient computed-RRR blocks.

This is a concrete route/class metadata envelope: the route-store words read
by each query are fixed-width encodings of the route fields, and the decoder is
fixed code over the charged read values. It still relies on the semantic route
records for correctness of the chosen route, but not for recovering the route
fields from metadata reads.
-/
structure FixedWeightAmbientComputedRRRPackedRouteTableData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  routeData :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost
  fieldWidth : Nat
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  accessBlockSlot : Nat -> Nat
  accessOffsetSlot : Nat -> Nat
  rankBlockSlot : Bool -> Nat -> Nat
  rankLocalLimitSlot : Bool -> Nat -> Nat
  rankBaseRankSlot : Bool -> Nat -> Nat
  selectBlockSlot : Bool -> Nat -> Nat
  selectLocalOccurrenceSlot : Bool -> Nat -> Nat
  selectBlockStartSlot : Bool -> Nat -> Nat
  access_metadata_reads_eq :
    forall i,
      (routeData.accessRoute i).metadataReads =
        [accessBlockSlot i, accessOffsetSlot i]
  rank_metadata_reads_eq :
    forall target pos,
      (routeData.rankRoute target pos).metadataReads =
        [rankBlockSlot target pos,
          rankLocalLimitSlot target pos,
          rankBaseRankSlot target pos]
  select_metadata_reads_eq :
    forall target occurrence,
      (routeData.selectRoute target occurrence).metadataReads =
        [selectBlockSlot target occurrence,
          selectLocalOccurrenceSlot target occurrence,
          selectBlockStartSlot target occurrence]
  access_block_lt :
    forall i, (routeData.accessRoute i).blockIndex < 2 ^ fieldWidth
  access_offset_lt :
    forall i, (routeData.accessRoute i).offset < 2 ^ fieldWidth
  rank_block_lt :
    forall target pos,
      (routeData.rankRoute target pos).blockIndex < 2 ^ fieldWidth
  rank_localLimit_lt :
    forall target pos,
      (routeData.rankRoute target pos).localLimit < 2 ^ fieldWidth
  rank_baseRank_lt :
    forall target pos,
      (routeData.rankRoute target pos).baseRank < 2 ^ fieldWidth
  select_block_lt :
    forall target occurrence,
      (routeData.selectRoute target occurrence).blockIndex < 2 ^ fieldWidth
  select_localOccurrence_lt :
    forall target occurrence,
      (routeData.selectRoute target occurrence).localOccurrence <
        2 ^ fieldWidth
  select_blockStart_lt :
    forall target occurrence,
      (routeData.selectRoute target occurrence).blockStart < 2 ^ fieldWidth
  access_block_word_eq :
    forall i,
      routeData.routeStore.store.words[accessBlockSlot i]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.accessRoute i).blockIndex)
  access_offset_word_eq :
    forall i,
      routeData.routeStore.store.words[accessOffsetSlot i]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.accessRoute i).offset)
  rank_block_word_eq :
    forall target pos,
      routeData.routeStore.store.words[rankBlockSlot target pos]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.rankRoute target pos).blockIndex)
  rank_localLimit_word_eq :
    forall target pos,
      routeData.routeStore.store.words[rankLocalLimitSlot target pos]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.rankRoute target pos).localLimit)
  rank_baseRank_word_eq :
    forall target pos,
      routeData.routeStore.store.words[rankBaseRankSlot target pos]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.rankRoute target pos).baseRank)
  select_block_word_eq :
    forall target occurrence,
      routeData.routeStore.store.words[selectBlockSlot target occurrence]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.selectRoute target occurrence).blockIndex)
  select_localOccurrence_word_eq :
    forall target occurrence,
      routeData.routeStore.store.words[
          selectLocalOccurrenceSlot target occurrence]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.selectRoute target occurrence).localOccurrence)
  select_blockStart_word_eq :
    forall target occurrence,
      routeData.routeStore.store.words[
          selectBlockStartSlot target occurrence]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.selectRoute target occurrence).blockStart)

namespace FixedWeightAmbientComputedRRRPackedRouteTableData

def toDecodedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRDecodedRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  wordSize_pos := data.routeData.wordSize_pos
  wordSize_le_ambient := data.routeData.wordSize_le_ambient
  blockSize := data.routeData.blockSize
  blockSize_pos := data.routeData.blockSize_pos
  blocks_flatten := data.routeData.blocks_flatten
  block_length_le := data.routeData.block_length_le
  blockSize_le_wordSize := data.routeData.blockSize_le_wordSize
  block_code_width_le := data.routeData.block_code_width_le
  codeStore := data.routeData.codeStore
  codeStore_aligned := data.routeData.codeStore_aligned
  routePayload := data.routeData.routePayload
  routeStore := data.routeData.routeStore
  routePayload_length_eq := data.routeData.routePayload_length_eq
  accessMetadataReads := fun i =>
    (data.routeData.accessRoute i).metadataReads
  rankMetadataReads := fun target pos =>
    (data.routeData.rankRoute target pos).metadataReads
  selectMetadataReads := fun target occurrence =>
    (data.routeData.selectRoute target occurrence).metadataReads
  accessRouteDecoder := fun _ readWords =>
    fixedWeightPackedRouteAccessDecoder readWords
  rankRouteDecoder := fun _ _ readWords =>
    fixedWeightPackedRouteRankDecoder readWords
  selectRouteDecoder := fun _ _ readWords =>
    fixedWeightPackedRouteSelectDecoder readWords
  accessRoute := data.routeData.accessRoute
  rankRoute := data.routeData.rankRoute
  selectRoute := data.routeData.selectRoute
  access_metadata_reads_le := data.routeData.access_metadata_reads_le
  rank_metadata_reads_le := data.routeData.rank_metadata_reads_le
  select_metadata_reads_le := data.routeData.select_metadata_reads_le
  access_route_metadata_reads_eq := by intro i; rfl
  rank_route_metadata_reads_eq := by intro target pos; rfl
  select_route_metadata_reads_eq := by intro target occurrence; rfl
  access_route_decode_exact := by
    intro i
    simp [fixedWeightPackedRouteAccessDecoder,
      boundedPayloadWordReadValues,
      data.access_metadata_reads_eq i,
      data.access_block_word_eq i,
      data.access_offset_word_eq i,
      data.access_block_lt i,
      data.access_offset_lt i,
      fixedWeightAmbientComputedRRRAccessRouteDecoded]
  rank_route_decode_exact := by
    intro target pos
    simp [fixedWeightPackedRouteRankDecoder,
      boundedPayloadWordReadValues,
      data.rank_metadata_reads_eq target pos,
      data.rank_block_word_eq target pos,
      data.rank_localLimit_word_eq target pos,
      data.rank_baseRank_word_eq target pos,
      data.rank_block_lt target pos,
      data.rank_localLimit_lt target pos,
      data.rank_baseRank_lt target pos,
      fixedWeightAmbientComputedRRRRankRouteDecoded]
  select_route_decode_exact := by
    intro target occurrence
    simp [fixedWeightPackedRouteSelectDecoder,
      boundedPayloadWordReadValues,
      data.select_metadata_reads_eq target occurrence,
      data.select_block_word_eq target occurrence,
      data.select_localOccurrence_word_eq target occurrence,
      data.select_blockStart_word_eq target occurrence,
      data.select_block_lt target occurrence,
      data.select_localOccurrence_lt target occurrence,
      data.select_blockStart_lt target occurrence,
      fixedWeightAmbientComputedRRRSelectRouteDecoded]
  local_query_cost_le := data.routeData.local_query_cost_le
  route_plus_local_le := data.routeData.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toDecodedRouteTableData.toAmbientBlockCompositionData

theorem access_packed_metadata_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    boundedPayloadWordReadValues data.routeData.routeStore
        (data.routeData.accessRoute i).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.accessRoute i).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.accessRoute i).offset)] := by
  simp [boundedPayloadWordReadValues,
    data.access_metadata_reads_eq i,
    data.access_block_word_eq i,
    data.access_offset_word_eq i]

theorem rank_packed_metadata_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    boundedPayloadWordReadValues data.routeData.routeStore
        (data.routeData.rankRoute target pos).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).localLimit),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).baseRank)] := by
  simp [boundedPayloadWordReadValues,
    data.rank_metadata_reads_eq target pos,
    data.rank_block_word_eq target pos,
    data.rank_localLimit_word_eq target pos,
    data.rank_baseRank_word_eq target pos]

theorem select_packed_metadata_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    boundedPayloadWordReadValues data.routeData.routeStore
        (data.routeData.selectRoute target occurrence).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).localOccurrence),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).blockStart)] := by
  simp [boundedPayloadWordReadValues,
    data.select_metadata_reads_eq target occurrence,
    data.select_block_word_eq target occurrence,
    data.select_localOccurrence_word_eq target occurrence,
    data.select_blockStart_word_eq target occurrence]

def PackedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toDecodedRouteTableData.DecodedRouteTableProfile /\
    data.toDecodedRouteTableData.DecodedMetadataReadProfile /\
    data.fieldWidth <= wordSize /\
    (forall i,
      (data.toDecodedRouteTableData.accessMetadataReadsCosted i).cost = 2 /\
        (Costed.map (fun words =>
            fixedWeightPackedRouteAccessDecoder words)
          (data.toDecodedRouteTableData.accessMetadataReadsCosted i)).erase =
          fixedWeightAmbientComputedRRRAccessRouteDecoded
            (data.routeData.accessRoute i)) /\
    (forall target pos,
      (data.toDecodedRouteTableData.rankMetadataReadsCosted
          target pos).cost = 3 /\
        (Costed.map (fun words =>
            fixedWeightPackedRouteRankDecoder words)
          (data.toDecodedRouteTableData.rankMetadataReadsCosted
            target pos)).erase =
          fixedWeightAmbientComputedRRRRankRouteDecoded
            (data.routeData.rankRoute target pos)) /\
    (forall target occurrence,
      (data.toDecodedRouteTableData.selectMetadataReadsCosted
          target occurrence).cost = 3 /\
        (Costed.map (fun words =>
            fixedWeightPackedRouteSelectDecoder words)
          (data.toDecodedRouteTableData.selectMetadataReadsCosted
            target occurrence)).erase =
          fixedWeightAmbientComputedRRRSelectRouteDecoded
            (data.routeData.selectRoute target occurrence))

theorem packed_route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.PackedRouteTableProfile := by
  refine
    ⟨data.toDecodedRouteTableData.decoded_route_table_profile,
      data.toDecodedRouteTableData.decoded_metadata_read_profile,
      data.fieldWidth_le_wordSize,
      ?_,
      ?_,
      ?_⟩
  · intro i
    constructor
    · simp [toDecodedRouteTableData,
        FixedWeightAmbientComputedRRRDecodedRouteTableData.accessMetadataReadsCosted,
        data.access_metadata_reads_eq i]
    · simpa [toDecodedRouteTableData] using
        (data.toDecodedRouteTableData.decoded_metadata_read_profile.1 i).2
  · intro target pos
    constructor
    · simp [toDecodedRouteTableData,
        FixedWeightAmbientComputedRRRDecodedRouteTableData.rankMetadataReadsCosted,
        data.rank_metadata_reads_eq target pos]
    · simpa [toDecodedRouteTableData] using
        (data.toDecodedRouteTableData.decoded_metadata_read_profile.2.1
          target pos).2
  · intro target occurrence
    constructor
    · simp [toDecodedRouteTableData,
        FixedWeightAmbientComputedRRRDecodedRouteTableData.selectMetadataReadsCosted,
        data.select_metadata_reads_eq target occurrence]
    · simpa [toDecodedRouteTableData] using
        (data.toDecodedRouteTableData.decoded_metadata_read_profile.2.2
          target occurrence).2

end FixedWeightAmbientComputedRRRPackedRouteTableData

/-- Family of packed fixed-width route/class metadata tables. -/
structure FixedWeightAmbientComputedRRRPackedRouteTableFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRPackedRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def toDecodedRouteTableFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRDecodedRouteTableFamily
      slots routeCost localQueryCost queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := (family.componentData bits).toDecodedRouteTableData

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toAmbientBlockCompositionData

theorem packed_route_table_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.PackedRouteTableProfile /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    exact
      ⟨data.packed_route_table_profile,
        data.routeData.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.routeData.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        (family.componentData bits).PackedRouteTableProfile /\
          let data := family.directory bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                compressedOverhead slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientComputedRRRDecodedRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family.toDecodedRouteTableFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead,
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily.compressedOverhead]
      using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).packed_route_table_profile
    · simpa [directory, toDecodedRouteTableFamily, componentData,
        FixedWeightAmbientComputedRRRDecodedRouteTableFamily.directory,
        FixedWeightAmbientComputedRRRDecodedRouteTableFamily.componentData,
        FixedWeightAmbientComputedRRRDecodedRouteTableFamily.compressedOverhead,
        compressedOverhead]
        using (hcompressed.2 bits).2

end FixedWeightAmbientComputedRRRPackedRouteTableFamily

theorem fixedWidthNatTableOfEntries_words_toList
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    (SuccinctSpace.FixedWidthNatTable.ofEntries
        entries width hbound).store.words.toList =
      entries.map (SuccinctSpace.natToBitsLE width) := by
  rfl

/--
Canonical fixed-width route-field table constructor for ambient computed-RRR.

The previous packed route layer assumed per-slot word equations. This layer
derives those equations from one canonical `FixedWidthNatTable.ofEntries`
payload table aligned with the route store.
-/
structure FixedWeightAmbientComputedRRRRouteFieldTablesData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  routeData :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost
  fieldWidth : Nat
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  routeFieldEntries : List Nat
  routeFieldEntries_bound :
    forall {entry : Nat}, List.Mem entry routeFieldEntries ->
      entry < 2 ^ fieldWidth
  routeStore_words_eq :
    routeData.routeStore.store.words.toList =
      (SuccinctSpace.FixedWidthNatTable.ofEntries
        routeFieldEntries fieldWidth routeFieldEntries_bound).store.words.toList
  accessBlockSlot : Nat -> Nat
  accessOffsetSlot : Nat -> Nat
  rankBlockSlot : Bool -> Nat -> Nat
  rankLocalLimitSlot : Bool -> Nat -> Nat
  rankBaseRankSlot : Bool -> Nat -> Nat
  selectBlockSlot : Bool -> Nat -> Nat
  selectLocalOccurrenceSlot : Bool -> Nat -> Nat
  selectBlockStartSlot : Bool -> Nat -> Nat
  access_metadata_reads_eq :
    forall i,
      (routeData.accessRoute i).metadataReads =
        [accessBlockSlot i, accessOffsetSlot i]
  rank_metadata_reads_eq :
    forall target pos,
      (routeData.rankRoute target pos).metadataReads =
        [rankBlockSlot target pos,
          rankLocalLimitSlot target pos,
          rankBaseRankSlot target pos]
  select_metadata_reads_eq :
    forall target occurrence,
      (routeData.selectRoute target occurrence).metadataReads =
        [selectBlockSlot target occurrence,
          selectLocalOccurrenceSlot target occurrence,
          selectBlockStartSlot target occurrence]
  access_block_entry_eq :
    forall i,
      routeFieldEntries[accessBlockSlot i]? =
        some (routeData.accessRoute i).blockIndex
  access_offset_entry_eq :
    forall i,
      routeFieldEntries[accessOffsetSlot i]? =
        some (routeData.accessRoute i).offset
  rank_block_entry_eq :
    forall target pos,
      routeFieldEntries[rankBlockSlot target pos]? =
        some (routeData.rankRoute target pos).blockIndex
  rank_localLimit_entry_eq :
    forall target pos,
      routeFieldEntries[rankLocalLimitSlot target pos]? =
        some (routeData.rankRoute target pos).localLimit
  rank_baseRank_entry_eq :
    forall target pos,
      routeFieldEntries[rankBaseRankSlot target pos]? =
        some (routeData.rankRoute target pos).baseRank
  select_block_entry_eq :
    forall target occurrence,
      routeFieldEntries[selectBlockSlot target occurrence]? =
        some (routeData.selectRoute target occurrence).blockIndex
  select_localOccurrence_entry_eq :
    forall target occurrence,
      routeFieldEntries[selectLocalOccurrenceSlot target occurrence]? =
        some (routeData.selectRoute target occurrence).localOccurrence
  select_blockStart_entry_eq :
    forall target occurrence,
      routeFieldEntries[selectBlockStartSlot target occurrence]? =
        some (routeData.selectRoute target occurrence).blockStart

namespace FixedWeightAmbientComputedRRRRouteFieldTablesData

def routeFieldTable
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    SuccinctSpace.FixedWidthNatTable
      data.routeFieldEntries data.fieldWidth :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    data.routeFieldEntries data.fieldWidth data.routeFieldEntries_bound

theorem routeFieldTable_words_toList
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.routeFieldTable.store.words.toList =
      data.routeFieldEntries.map
        (SuccinctSpace.natToBitsLE data.fieldWidth) := by
  exact fixedWidthNatTableOfEntries_words_toList
    data.routeFieldEntries data.fieldWidth data.routeFieldEntries_bound

theorem routeFieldEntry_lt_of_get?
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {slot value : Nat}
    (hget : data.routeFieldEntries[slot]? = some value) :
    value < 2 ^ data.fieldWidth := by
  exact data.routeFieldEntries_bound (List.mem_of_getElem? hget)

theorem routeStore_word_eq_of_entry_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {slot value : Nat}
    (hget : data.routeFieldEntries[slot]? = some value) :
    data.routeData.routeStore.store.words[slot]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth value) := by
  have hlist :
      data.routeData.routeStore.store.words.toList[slot]? =
        some (SuccinctSpace.natToBitsLE data.fieldWidth value) := by
    rw [data.routeStore_words_eq,
      fixedWidthNatTableOfEntries_words_toList
        data.routeFieldEntries data.fieldWidth
        data.routeFieldEntries_bound]
    simp [List.getElem?_map, hget]
  simpa [Array.getElem?_toList] using hlist

def toPackedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  routeData := data.routeData
  fieldWidth := data.fieldWidth
  fieldWidth_le_wordSize := data.fieldWidth_le_wordSize
  accessBlockSlot := data.accessBlockSlot
  accessOffsetSlot := data.accessOffsetSlot
  rankBlockSlot := data.rankBlockSlot
  rankLocalLimitSlot := data.rankLocalLimitSlot
  rankBaseRankSlot := data.rankBaseRankSlot
  selectBlockSlot := data.selectBlockSlot
  selectLocalOccurrenceSlot := data.selectLocalOccurrenceSlot
  selectBlockStartSlot := data.selectBlockStartSlot
  access_metadata_reads_eq := data.access_metadata_reads_eq
  rank_metadata_reads_eq := data.rank_metadata_reads_eq
  select_metadata_reads_eq := data.select_metadata_reads_eq
  access_block_lt := fun i =>
    data.routeFieldEntry_lt_of_get? (data.access_block_entry_eq i)
  access_offset_lt := fun i =>
    data.routeFieldEntry_lt_of_get? (data.access_offset_entry_eq i)
  rank_block_lt := fun target pos =>
    data.routeFieldEntry_lt_of_get?
      (data.rank_block_entry_eq target pos)
  rank_localLimit_lt := fun target pos =>
    data.routeFieldEntry_lt_of_get?
      (data.rank_localLimit_entry_eq target pos)
  rank_baseRank_lt := fun target pos =>
    data.routeFieldEntry_lt_of_get?
      (data.rank_baseRank_entry_eq target pos)
  select_block_lt := fun target occurrence =>
    data.routeFieldEntry_lt_of_get?
      (data.select_block_entry_eq target occurrence)
  select_localOccurrence_lt := fun target occurrence =>
    data.routeFieldEntry_lt_of_get?
      (data.select_localOccurrence_entry_eq target occurrence)
  select_blockStart_lt := fun target occurrence =>
    data.routeFieldEntry_lt_of_get?
      (data.select_blockStart_entry_eq target occurrence)
  access_block_word_eq := fun i =>
    data.routeStore_word_eq_of_entry_eq
      (data.access_block_entry_eq i)
  access_offset_word_eq := fun i =>
    data.routeStore_word_eq_of_entry_eq
      (data.access_offset_entry_eq i)
  rank_block_word_eq := fun target pos =>
    data.routeStore_word_eq_of_entry_eq
      (data.rank_block_entry_eq target pos)
  rank_localLimit_word_eq := fun target pos =>
    data.routeStore_word_eq_of_entry_eq
      (data.rank_localLimit_entry_eq target pos)
  rank_baseRank_word_eq := fun target pos =>
    data.routeStore_word_eq_of_entry_eq
      (data.rank_baseRank_entry_eq target pos)
  select_block_word_eq := fun target occurrence =>
    data.routeStore_word_eq_of_entry_eq
      (data.select_block_entry_eq target occurrence)
  select_localOccurrence_word_eq := fun target occurrence =>
    data.routeStore_word_eq_of_entry_eq
      (data.select_localOccurrence_entry_eq target occurrence)
  select_blockStart_word_eq := fun target occurrence =>
    data.routeStore_word_eq_of_entry_eq
      (data.select_blockStart_entry_eq target occurrence)

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toPackedRouteTableData.toAmbientBlockCompositionData

def RouteFieldTablesProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toPackedRouteTableData.PackedRouteTableProfile /\
    data.routeFieldTable.payload.length =
      data.routeFieldEntries.length * data.fieldWidth /\
    SuccinctSpace.flattenPayloadWords
        data.routeFieldTable.store.words.toList =
      data.routeFieldTable.payload /\
    data.routeData.routeStore.store.words.toList =
      data.routeFieldTable.store.words.toList

theorem route_field_tables_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteFieldTablesProfile := by
  exact
    ⟨data.toPackedRouteTableData.packed_route_table_profile,
      data.routeFieldTable.payload_length,
      data.routeFieldTable.store.payload_eq_words_join,
      data.routeStore_words_eq⟩

theorem route_field_tables_packed_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteFieldTablesProfile := by
  exact data.route_field_tables_profile

end FixedWeightAmbientComputedRRRRouteFieldTablesData

/-- Family of canonical fixed-width route-field table constructors. -/
structure FixedWeightAmbientComputedRRRRouteFieldTablesFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRRouteFieldTablesData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRRouteFieldTablesFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRRouteFieldTablesData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def toPackedRouteTableFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableFamily
      slots routeCost localQueryCost queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := (family.componentData bits).toPackedRouteTableData

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toAmbientBlockCompositionData

theorem route_field_tables_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.RouteFieldTablesProfile /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    exact
      ⟨data.route_field_tables_profile,
        data.routeData.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.routeData.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTablesFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        (family.componentData bits).RouteFieldTablesProfile /\
          let data := family.directory bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                compressedOverhead slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientComputedRRRPackedRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family.toPackedRouteTableFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead,
      FixedWeightAmbientComputedRRRPackedRouteTableFamily.compressedOverhead]
      using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).route_field_tables_profile
    · simpa [directory, toPackedRouteTableFamily, componentData,
        FixedWeightAmbientComputedRRRPackedRouteTableFamily.directory,
        FixedWeightAmbientComputedRRRPackedRouteTableFamily.componentData,
        FixedWeightAmbientComputedRRRPackedRouteTableFamily.compressedOverhead,
        compressedOverhead]
        using (hcompressed.2 bits).2

end FixedWeightAmbientComputedRRRRouteFieldTablesFamily

end RankSelectSpec

end RMQ

import RMQ.Core.RankSelectCompressed.Base.Core.LocalRRR

namespace RMQ

namespace RankSelectSpec

/--
Access routing metadata for the ambient computed-RRR predecessor.

The metadata read list is charged through the ambient auxiliary store. The
semantic fields identify the routed block/offset; a later fully built FID
construction should derive these fields from concrete payload tables.
-/
structure FixedWeightAmbientComputedRRRAccessRoute
    (bits : List Bool) (blocks : List (List Bool)) (i : Nat) where
  blockIndex : Nat
  block : List Bool
  block_get : blocks[blockIndex]? = some block
  offset : Nat
  metadataReads : List Nat
  access_exact : block[offset]? = bits[i]?

/-- Rank routing metadata for the ambient computed-RRR predecessor. -/
structure FixedWeightAmbientComputedRRRRankRoute
    (bits : List Bool) (blocks : List (List Bool))
    (target : Bool) (pos : Nat) where
  blockIndex : Nat
  block : List Bool
  block_get : blocks[blockIndex]? = some block
  localLimit : Nat
  baseRank : Nat
  metadataReads : List Nat
  rank_exact :
    baseRank + Succinct.rankPrefix target block localLimit =
      Succinct.rankPrefix target bits pos

/-- Select routing metadata for the ambient computed-RRR predecessor. -/
structure FixedWeightAmbientComputedRRRSelectRoute
    (bits : List Bool) (blocks : List (List Bool))
    (target : Bool) (occurrence : Nat) where
  blockIndex : Nat
  block : List Bool
  block_get : blocks[blockIndex]? = some block
  localOccurrence : Nat
  blockStart : Nat
  metadataReads : List Nat
  select_exact :
    (Succinct.select target block localOccurrence).map
        (fun offset => blockStart + offset) =
      Succinct.select target bits occurrence

/--
Ambient/global block-composition data whose local block backend is the
computed packed-code-only fixed-weight/RRR kernel.

The primary payload is still `fixedWeightBlockCodePayload blocks`. Routing and
class metadata are charged by `metadataReads` through the auxiliary store; the
local block decoder is governed by the uniform `localQueryCost` bound. This is
the concrete predecessor needed before proving that a particular routing/class
table construction has `o(n)` payload and truly constant local decode cost.
-/
structure FixedWeightAmbientComputedRRRBlockData
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
  auxPayload : List Bool
  auxStore :
    SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize
  aux_length_eq : auxPayload.length = overhead
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
    forall i, (accessRoute i).metadataReads.length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankRoute target pos).metadataReads.length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads.length <= routeCost
  local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost
  route_plus_local_le : routeCost + localQueryCost <= queryCost

namespace FixedWeightAmbientComputedRRRBlockData

def localBlockData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    FixedWeightComputedRRRBlockData bits.length block wordSize where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  codeWidth_le_wordSize :=
    data.block_code_width_le (List.mem_of_getElem? hblock)
  blockWidth_le_wordSize :=
    Nat.le_trans
      (data.block_length_le (List.mem_of_getElem? hblock))
      data.blockSize_le_wordSize

theorem code_read_values_singleton
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.codeStore [blockIndex] =
      [some (fixedWeightPackedPayload block)] := by
  have hget :
      data.codeStore.store.words[blockIndex]? =
        some (fixedWeightPackedPayload block) :=
    fixedWeightAmbientBlockCodeStore_get?_of_aligned
      data.codeStore_aligned hblock
  simp [boundedPayloadWordReadValues, hget]

def accessEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) (codeWords auxWords : List (Option (List Bool))) :
    Costed (Option Bool) :=
  let route := data.accessRoute i
  ((data.localBlockData route.block_get).toDependentAuxiliaryData).accessEvalCosted
    route.offset codeWords auxWords

def rankEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat)
    (codeWords auxWords : List (Option (List Bool))) :
    Costed Nat :=
  let route := data.rankRoute target pos
  Costed.map (fun localRank => route.baseRank + localRank)
    (((data.localBlockData route.block_get).toDependentAuxiliaryData).rankEvalCosted
      target route.localLimit codeWords auxWords)

def selectEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat)
    (codeWords auxWords : List (Option (List Bool))) :
    Costed (Option Nat) :=
  let route := data.selectRoute target occurrence
  Costed.map (fun local? =>
      local?.map (fun offset => route.blockStart + offset))
    (((data.localBlockData route.block_get).toDependentAuxiliaryData).selectEvalCosted
      target route.localOccurrence codeWords auxWords)

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost := by
  refine
    { wordSize_pos := data.wordSize_pos
      wordSize_le_ambient := data.wordSize_le_ambient
      blockSize := data.blockSize
      blockSize_pos := data.blockSize_pos
      blocks_flatten := data.blocks_flatten
      block_length_le := data.block_length_le
      blockSize_le_wordSize := data.blockSize_le_wordSize
      block_code_width_le := data.block_code_width_le
      codeStore := data.codeStore
      auxPayload := data.auxPayload
      auxStore := data.auxStore
      aux_length_eq := data.aux_length_eq
      accessCodeReads := fun i => [(data.accessRoute i).blockIndex]
      accessAuxReads := fun i _ => (data.accessRoute i).metadataReads
      rankCodeReads := fun target pos =>
        [(data.rankRoute target pos).blockIndex]
      rankAuxReads := fun target pos _ =>
        (data.rankRoute target pos).metadataReads
      selectCodeReads := fun target occurrence =>
        [(data.selectRoute target occurrence).blockIndex]
      selectAuxReads := fun target occurrence _ =>
        (data.selectRoute target occurrence).metadataReads
      accessEvalCosted := data.accessEvalCosted
      rankEvalCosted := data.rankEvalCosted
      selectEvalCosted := data.selectEvalCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · intro i
    let route := data.accessRoute i
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hroute := data.access_metadata_reads_le i
    have hlocal := data.local_query_cost_le hmem
    have htotal := data.route_plus_local_le
    simp [accessEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      fixedWeightComputedRRRDecodeFromReadValuesCosted,
      fixedWeightComputedRRRQueryCost] at *
    omega
  · intro target pos
    let route := data.rankRoute target pos
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hroute := data.rank_metadata_reads_le target pos
    have hlocal := data.local_query_cost_le hmem
    have htotal := data.route_plus_local_le
    simp [rankEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      fixedWeightComputedRRRDecodeFromReadValuesCosted,
      fixedWeightComputedRRRQueryCost] at *
    omega
  · intro target occurrence
    let route := data.selectRoute target occurrence
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hroute := data.select_metadata_reads_le target occurrence
    have hlocal := data.local_query_cost_le hmem
    have htotal := data.route_plus_local_le
    simp [selectEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      fixedWeightComputedRRRDecodeFromReadValuesCosted,
      fixedWeightComputedRRRQueryCost] at *
    omega
  · intro i
    let route := data.accessRoute i
    have hread := data.code_read_values_singleton route.block_get
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
        route.block
    simp [accessEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData, hread,
      hdecode, route.access_exact]
  · intro target pos
    let route := data.rankRoute target pos
    have hread := data.code_read_values_singleton route.block_get
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
        route.block
    have hrun :=
      Succinct.rankBoolWordPrefix_toCosted_run
        target route.block route.localLimit
    simp only [rankEvalCosted, Costed.erase_map,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      Costed.erase_bind]
    change
      route.baseRank +
          (RAM.rankBoolWordPrefix target
              (fixedWeightComputedRRRDecodeFromReadValuesCosted
                route.block
                (boundedPayloadWordReadValues data.codeStore
                  [route.blockIndex])).erase
              route.localLimit).toCosted.erase =
        Succinct.rankPrefix target bits pos
    rw [hread]
    rw [hdecode]
    change
      route.baseRank +
          (RAM.rankBoolWordPrefix target route.block route.localLimit).toCosted.value =
        Succinct.rankPrefix target bits pos
    have hram :
        (RAM.rankBoolWordPrefix target route.block route.localLimit).toCosted.value =
          Succinct.rankPrefix target route.block route.localLimit := by
      simpa [Costed.run] using congrArg Prod.fst hrun
    rw [hram]
    exact route.rank_exact
  · intro target occurrence
    let route := data.selectRoute target occurrence
    have hread := data.code_read_values_singleton route.block_get
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
        route.block
    have hrun :=
      Succinct.selectBoolWord_toCosted_run
        target route.block route.localOccurrence
    simp only [selectEvalCosted, Costed.erase_map,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      Costed.erase_bind]
    change
      ((RAM.selectBoolWord target
              (fixedWeightComputedRRRDecodeFromReadValuesCosted
                route.block
                (boundedPayloadWordReadValues data.codeStore
                  [route.blockIndex])).erase
              route.localOccurrence).toCosted.erase).map
          (fun offset => route.blockStart + offset) =
        Succinct.select target bits occurrence
    rw [hread]
    rw [hdecode]
    change
      ((RAM.selectBoolWord target route.block route.localOccurrence).toCosted.value).map
          (fun offset => route.blockStart + offset) =
        Succinct.select target bits occurrence
    have hselect :
        (RAM.selectBoolWord target route.block route.localOccurrence).toCosted.value =
          Succinct.select target route.block route.localOccurrence := by
      simpa [Costed.run] using congrArg Prod.fst hrun
    rw [hselect]
    exact route.select_exact

def CompositionProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  (data.toAmbientBlockCompositionData).DirectoryProfile /\
    data.codeStore.store.words.toList = fixedWeightBlockCodeWords blocks /\
    (forall i,
      let route := data.accessRoute i
      boundedPayloadWordReadValues data.codeStore [route.blockIndex] =
          [some (fixedWeightPackedPayload route.block)] /\
        ((data.localBlockData route.block_get).toDependentAuxiliaryData).DirectoryProfile /\
        route.metadataReads.length <= routeCost) /\
    (forall target pos,
      let route := data.rankRoute target pos
      boundedPayloadWordReadValues data.codeStore [route.blockIndex] =
          [some (fixedWeightPackedPayload route.block)] /\
        ((data.localBlockData route.block_get).toDependentAuxiliaryData).DirectoryProfile /\
        route.metadataReads.length <= routeCost) /\
    (forall target occurrence,
      let route := data.selectRoute target occurrence
      boundedPayloadWordReadValues data.codeStore [route.blockIndex] =
          [some (fixedWeightPackedPayload route.block)] /\
        ((data.localBlockData route.block_get).toDependentAuxiliaryData).DirectoryProfile /\
        route.metadataReads.length <= routeCost) /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost) /\
    routeCost + localQueryCost <= queryCost

theorem computed_rrr_block_composition_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.CompositionProfile := by
  refine
    ⟨data.toAmbientBlockCompositionData.directory_profile,
      data.codeStore_aligned,
      ?_,
      ?_,
      ?_,
      data.local_query_cost_le,
      data.route_plus_local_le⟩
  · intro i
    exact
      ⟨data.code_read_values_singleton (data.accessRoute i).block_get,
        FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
          (data.localBlockData (data.accessRoute i).block_get),
        data.access_metadata_reads_le i⟩
  · intro target pos
    exact
      ⟨data.code_read_values_singleton
          (data.rankRoute target pos).block_get,
        FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
          (data.localBlockData (data.rankRoute target pos).block_get),
        data.rank_metadata_reads_le target pos⟩
  · intro target occurrence
    exact
      ⟨data.code_read_values_singleton
          (data.selectRoute target occurrence).block_get,
        FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
          (data.localBlockData
            (data.selectRoute target occurrence).block_get),
        data.select_metadata_reads_le target occurrence⟩

end FixedWeightAmbientComputedRRRBlockData

/--
Payload-backed route/class metadata tables for ambient computed-RRR blocks.

This layer owns the auxiliary route payload and bounded route store, then
instantiates `FixedWeightAmbientComputedRRRBlockData`. The route records still
carry the semantic facts needed to identify the chosen block and local query;
the important extra discipline here is that every such route is backed by a
counted metadata read schedule over this concrete payload store.
-/
structure FixedWeightAmbientComputedRRRRouteTableData
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
    forall i, (accessRoute i).metadataReads.length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankRoute target pos).metadataReads.length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads.length <= routeCost
  local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost
  route_plus_local_le : routeCost + localQueryCost <= queryCost

namespace FixedWeightAmbientComputedRRRRouteTableData

def toComputedRRRBlockData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRBlockData
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
  auxPayload := data.routePayload
  auxStore := data.routeStore
  aux_length_eq := data.routePayload_length_eq
  accessRoute := data.accessRoute
  rankRoute := data.rankRoute
  selectRoute := data.selectRoute
  access_metadata_reads_le := data.access_metadata_reads_le
  rank_metadata_reads_le := data.rank_metadata_reads_le
  select_metadata_reads_le := data.select_metadata_reads_le
  local_query_cost_le := data.local_query_cost_le
  route_plus_local_le := data.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toComputedRRRBlockData.toAmbientBlockCompositionData

def accessMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.accessRoute i).metadataReads

def rankMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.rankRoute target pos).metadataReads

def selectMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.selectRoute target occurrence).metadataReads

def RouteTableReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  (forall i,
    (data.accessMetadataReadsCosted i).cost <= routeCost /\
      (data.accessMetadataReadsCosted i).erase =
        boundedPayloadWordReadValues data.routeStore
          (data.accessRoute i).metadataReads) /\
    (forall target pos,
      (data.rankMetadataReadsCosted target pos).cost <= routeCost /\
        (data.rankMetadataReadsCosted target pos).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.rankRoute target pos).metadataReads) /\
    (forall target occurrence,
      (data.selectMetadataReadsCosted target occurrence).cost <=
          routeCost /\
        (data.selectMetadataReadsCosted target occurrence).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.selectRoute target occurrence).metadataReads)

theorem route_table_read_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteTableReadProfile := by
  exact
    ⟨(fun i => by
        constructor
        · dsimp [accessMetadataReadsCosted]
          simpa using data.access_metadata_reads_le i
        · simp [accessMetadataReadsCosted]),
      (fun target pos => by
        constructor
        · dsimp [rankMetadataReadsCosted]
          simpa using data.rank_metadata_reads_le target pos
        · simp [rankMetadataReadsCosted]),
      (fun target occurrence => by
        constructor
        · dsimp [selectMetadataReadsCosted]
          simpa using data.select_metadata_reads_le target occurrence
        · simp [selectMetadataReadsCosted])⟩

def RouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toComputedRRRBlockData.CompositionProfile /\
    data.RouteTableReadProfile /\
    data.routePayload.length = overhead /\
    SuccinctSpace.flattenPayloadWords data.routeStore.store.words.toList =
      data.routePayload /\
    (forall {word : List Bool},
      List.Mem word data.routeStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      let route := data.accessRoute i
      (boundedPayloadWordReadValues
          data.routeStore route.metadataReads).length <= routeCost) /\
    (forall target pos,
      let route := data.rankRoute target pos
      (boundedPayloadWordReadValues
          data.routeStore route.metadataReads).length <= routeCost) /\
    (forall target occurrence,
      let route := data.selectRoute target occurrence
      (boundedPayloadWordReadValues
          data.routeStore route.metadataReads).length <= routeCost) /\
    (forall i, (data.accessRoute i).metadataReads.length <= routeCost) /\
    (forall target pos,
      (data.rankRoute target pos).metadataReads.length <= routeCost) /\
    (forall target occurrence,
      (data.selectRoute target occurrence).metadataReads.length <=
        routeCost) /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost) /\
    routeCost + localQueryCost <= queryCost

theorem route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteTableProfile := by
  exact
    ⟨data.toComputedRRRBlockData.computed_rrr_block_composition_profile,
      data.route_table_read_profile,
      data.routePayload_length_eq,
      data.routeStore.erases,
      (fun hmem => data.routeStore.word_length_le_of_mem hmem),
      (fun i => by
        dsimp [boundedPayloadWordReadValues]
        simpa using data.access_metadata_reads_le i),
      (fun target pos => by
        dsimp [boundedPayloadWordReadValues]
        simpa using data.rank_metadata_reads_le target pos),
      (fun target occurrence => by
        dsimp [boundedPayloadWordReadValues]
        simpa using data.select_metadata_reads_le target occurrence),
      data.access_metadata_reads_le,
      data.rank_metadata_reads_le,
      data.select_metadata_reads_le,
      data.local_query_cost_le,
      data.route_plus_local_le⟩

end FixedWeightAmbientComputedRRRRouteTableData

/--
Payload-backed route/class metadata tables whose local computed-RRR query cost
is derived from a uniform block-size bound.

This is the non-oracular constructor-oriented variant of
`FixedWeightAmbientComputedRRRRouteTableData`: the caller supplies concrete
route metadata and a proof that every block has length at most `blockSize`, and
the local query-cost premise is generated from
`fixedWeightComputedRRRQueryCost_le_blockSize`.
-/
structure FixedWeightAmbientComputedRRRBlockSizeRouteTableData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize blockSize routeCost queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
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
    forall i, (accessRoute i).metadataReads.length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankRoute target pos).metadataReads.length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads.length <= routeCost
  route_plus_local_le :
    routeCost + fixedWeightComputedRRRBlockSizeQueryCost blockSize <=
      queryCost

namespace FixedWeightAmbientComputedRRRBlockSizeRouteTableData

def localQueryCost (blockSize : Nat) : Nat :=
  fixedWeightComputedRRRBlockSizeQueryCost blockSize

def toRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize blockSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits blocks overhead wordSize blockSize routeCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost
        (localQueryCost blockSize) queryCost where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  blockSize := blockSize
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
  access_metadata_reads_le := data.access_metadata_reads_le
  rank_metadata_reads_le := data.rank_metadata_reads_le
  select_metadata_reads_le := data.select_metadata_reads_le
  local_query_cost_le := by
    intro block hmem
    exact
      fixedWeightComputedRRRQueryCost_le_blockSize
        (bits := block) (data.block_length_le hmem)
  route_plus_local_le := data.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize blockSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits blocks overhead wordSize blockSize routeCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toRouteTableData.toAmbientBlockCompositionData

def BlockSizeRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize blockSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits blocks overhead wordSize blockSize routeCost queryCost) :
    Prop :=
  data.toRouteTableData.RouteTableProfile /\
    data.routePayload.length = overhead /\
    (data.toAmbientBlockCompositionData).payload.length =
      fixedWeightBlockPayloadBudget blocks + overhead /\
    SuccinctSpace.flattenPayloadWords blocks = bits /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <=
        fixedWeightComputedRRRBlockSizeQueryCost blockSize) /\
    routeCost + fixedWeightComputedRRRBlockSizeQueryCost blockSize <=
      queryCost

theorem block_size_route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize blockSize routeCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits blocks overhead wordSize blockSize routeCost queryCost) :
    data.BlockSizeRouteTableProfile := by
  exact
    ⟨data.toRouteTableData.route_table_profile,
      data.routePayload_length_eq,
      data.toAmbientBlockCompositionData.payload_length,
      data.blocks_flatten,
      (fun hmem =>
        fixedWeightComputedRRRQueryCost_le_blockSize
          (bits := _) (data.block_length_le hmem)),
      data.route_plus_local_le⟩

end FixedWeightAmbientComputedRRRBlockSizeRouteTableData

/--
Family of ambient computed-RRR route/class metadata tables.

The family-level overhead is the ambient `o(n)` envelope; each pointwise
component stores the concrete route/class metadata payload in a bounded store
and consumes it through `FixedWeightAmbientComputedRRRBlockData`.
-/
structure FixedWeightAmbientComputedRRRRouteTableFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
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
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionFamily slots queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := family.directory bits

theorem route_table_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.RouteTableProfile /\
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
    have hprofile := data.route_table_profile
    exact
      ⟨hprofile,
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
      FixedWeightAmbientComputedRRRRouteTableFamily
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
        let routeData := family.componentData bits
        let data := family.directory bits
        routeData.RouteTableProfile /\
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
    · exact (family.componentData bits).route_table_profile
    · simpa [directory, toAmbientBlockCompositionFamily, componentData,
        compressedOverhead] using hcompressed.2 bits

end FixedWeightAmbientComputedRRRRouteTableFamily

/--
Family of route/class metadata tables with a fixed ambient block-size cap.

The local computed-RRR query bound is the explicit constant
`2 ^ blockSize + blockSize + 2`; every pointwise component proves the block
length discipline needed to discharge that bound.
-/
structure FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
    (slots blockSize routeCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRBlockSizeRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) blockSize routeCost queryCost

namespace FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def localQueryCost (blockSize : Nat) : Nat :=
  fixedWeightComputedRRRBlockSizeQueryCost blockSize

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientComputedRRRRouteTableFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRBlockSizeRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) blockSize routeCost queryCost :=
  family.component bits

def toRouteTableFamily
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableFamily
      slots routeCost (localQueryCost blockSize) queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := (family.componentData bits).toRouteTableData

def directory
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  FixedWeightAmbientComputedRRRRouteTableFamily.directory
    family.toRouteTableFamily bits

theorem block_size_route_table_family_profile
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.BlockSizeRouteTableProfile /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {block : List Bool},
            List.Mem block (family.blocks bits) ->
              fixedWeightComputedRRRQueryCost block <=
                localQueryCost blockSize) /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost /\
            ((family.directory bits).accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost /\
            ((family.directory bits).rankCosted target pos).erase =
              Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost /\
            ((family.directory bits).selectCosted target occurrence).erase =
              Succinct.select target bits occurrence) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    have hprofile := data.block_size_route_table_profile
    exact
      ⟨hprofile,
        (family.directory bits).payload_length,
        data.blocks_flatten,
        (fun hmem =>
          fixedWeightComputedRRRQueryCost_le_blockSize
            (bits := _) (data.block_length_le hmem)),
        (fun i =>
          ⟨(family.directory bits).accessCosted_cost_le i,
            (family.directory bits).accessCosted_erase i⟩),
        (fun target pos =>
          ⟨(family.directory bits).rankCosted_cost_le target pos,
            (family.directory bits).rankCosted_erase target pos⟩),
        (fun target occurrence =>
          ⟨(family.directory bits).selectCosted_cost_le target occurrence,
            (family.directory bits).selectCosted_erase
              target occurrence⟩)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots blockSize routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily
        slots blockSize routeCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        let blockSizeData := family.componentData bits
        let routeData := blockSizeData.toRouteTableData
        let data := family.directory bits
        blockSizeData.BlockSizeRouteTableProfile /\
          routeData.RouteTableProfile /\
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
    FixedWeightAmbientComputedRRRRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family.toRouteTableFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead] using hcompressed.1
  · intro bits
    let blockSizeData := family.componentData bits
    have hblock := blockSizeData.block_size_route_table_profile
    have hroute := hcompressed.2 bits
    exact
      ⟨hblock,
        by
          simpa [toRouteTableFamily, componentData] using hroute.1,
        by
          simpa [directory, toRouteTableFamily, componentData,
            compressedOverhead] using hroute.2⟩

end FixedWeightAmbientComputedRRRBlockSizeRouteTableFamily

end RankSelectSpec

end RMQ

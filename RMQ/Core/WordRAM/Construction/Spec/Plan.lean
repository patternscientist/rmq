import RMQ.Core.WordRAM.Packed.Allocation

/-!
# PRE-1 S1: the emission plan of `buildMemory`

Machine-free specification layer (outside the builder firewall; nothing in the
operational closure imports it, and it contains no builder program text).

`PackedWordRAM.buildMemory xs` is defined through `shapeMemory`,
`repackWords`, `packedReviewerMemory` (a chunking of the padded bit string into
old-width cells) and the canonical reviewer payload, whose leaves are
proof-carrying table structures. This module states the same list as an
explicit, ordered emission plan in which every leaf is a named reference object:

1. 174 metadata words `metadataOf n lc sc`, a function of the three scalars
   `n = xs.length`, `lc = longCount shape`, `sc = packedReviewerSparseCount shape`
   only (`metadata_eq_metadataOf` is `rfl`);
2. the dense repacking, at `W = wordWidth n`, of the old bit string, which is
   * the old header `natToBitsLE oldW lc` (`oldW = packedReviewerCellWidth n`),
   * the BP code,
   * the 18 live access sources (`accessSegments`),
   * the eight interior tables (`interiorSegments`),
   * the fringe and select-chunk microtables,
   * the first zero padding up to `cellCount * oldW`,
   followed by the second zero padding up to `denseCount * W`.

Every table leaf is `tableBits entries width`, the fixed-width little-endian
encoding of its reference entry list; `FixedWidthNatTable.payload_eq_tableBits`
proves this for every table structure whatever its construction. The two raw
leaves are `GenericSelect.longSuperFlagBits` and the EFFECTIVE sparse-exception
flag vector `GenericSelect.sparseExceptionEffectiveFlagBits` (not
`sparseFlagBits`); the sparse flag-rank tables are over that effective vector.

All statements are universal over `xs : List Int` (degenerate layouts, e.g.
`n ∈ {0, 1, 2, 3}`, are instances, not special cases). The reference
definitions appear only on right-hand sides; the charged builder never calls
them.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.SuccinctSpace
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

/-! ## Fixed-width table encoding -/

/-- The payload bits of a fixed-width table over `entries`: each entry encoded
in exactly `width` little-endian bits, concatenated in entry order. -/
def tableBits (entries : List Nat) (width : Nat) : List Bool :=
  flattenPayloadWords (entries.map (natToBitsLE width))

theorem natToBitsLE_length_bitsToNatLE : ∀ word : List Bool,
    natToBitsLE word.length (bitsToNatLE word) = word
  | [] => rfl
  | false :: rest => by
      have ih := natToBitsLE_length_bitsToNatLE rest
      show decide ((0 + 2 * bitsToNatLE rest) % 2 = 1) ::
          natToBitsLE rest.length ((0 + 2 * bitsToNatLE rest) / 2) = false :: rest
      rw [show (0 + 2 * bitsToNatLE rest) % 2 = 0 by omega,
        show (0 + 2 * bitsToNatLE rest) / 2 = bitsToNatLE rest by omega, ih]
      rfl
  | true :: rest => by
      have ih := natToBitsLE_length_bitsToNatLE rest
      show decide ((1 + 2 * bitsToNatLE rest) % 2 = 1) ::
          natToBitsLE rest.length ((1 + 2 * bitsToNatLE rest) / 2) = true :: rest
      rw [show (1 + 2 * bitsToNatLE rest) % 2 = 1 by omega,
        show (1 + 2 * bitsToNatLE rest) / 2 = bitsToNatLE rest by omega, ih]
      rfl

/-- **Table payload law.** Every `FixedWidthNatTable entries width`, however it
was built, stores exactly `tableBits entries width`. -/
theorem FixedWidthNatTable.payload_eq_tableBits {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.payload = tableBits entries width := by
  rw [← table.store.erases]
  unfold tableBits
  congr 1
  apply List.ext_getElem?
  intro i
  have hread := table.read_exact i
  rw [List.getElem?_map, Array.getElem?_toList]
  cases hword : table.store.words[i]? with
  | none =>
      rw [hword] at hread
      simp only [Option.map_none] at hread
      rw [← hread]
      rfl
  | some word =>
      rw [hword] at hread
      simp only [Option.map_some] at hread
      rw [← hread, Option.map_some, ← table.word_length_of_get? hword,
        natToBitsLE_length_bitsToNatLE]

/-! ## Named payload segments -/

/-- The 18 live access sources of the canonical reviewer payload, in payload
order (FlatPayload.lean `concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources`):
final rank super/block (false), select super fields ×4, select local fields ×4,
long-flag rank super/block (true), long flags, long relative offsets,
sparse-flag rank super/block (true), effective sparse flags, sparse relative
offsets. -/
def accessSegments (shape : CartesianShape) : List (List Bool) :=
  let b := shape.bpCode
  let ws := SuccinctRank.machineWordBits b.length
  let longBits := GenericSelect.longSuperFlagBits b false
  let longWs := SuccinctRank.machineWordBits longBits.length
  let sparseBits := GenericSelect.sparseExceptionEffectiveFlagBits b false
  let sparseWs := SuccinctRank.machineWordBits sparseBits.length
  let superE := GenericSelect.superEntries b false
  let localE := GenericSelect.localEntries b false
  [ tableBits (SuccinctRank.canonicalSuperRankEntries false b ws ws) ws,
    tableBits (SuccinctRank.canonicalBlockRankEntries false b ws ws)
      (SuccinctRank.machineWordBits (ws * ws)),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences superE)
      (GenericSelect.superFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices superE)
      (GenericSelect.superFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore superE)
      (GenericSelect.superFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets superE)
      (GenericSelect.superFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences localE)
      (GenericSelect.localFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices localE)
      (GenericSelect.localFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore localE)
      (GenericSelect.localFieldWidth b),
    tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets localE)
      (GenericSelect.localFieldWidth b),
    tableBits (SuccinctRank.canonicalSuperRankEntries true longBits longWs 1) longWs,
    tableBits (SuccinctRank.canonicalBlockRankEntries true longBits longWs 1) longWs,
    longBits,
    tableBits (GenericSelect.longSuperRelativeEntries b false)
      (GenericSelect.longSuperRelativeWidth b),
    tableBits (SuccinctRank.canonicalSuperRankEntries true sparseBits sparseWs 1) sparseWs,
    tableBits (SuccinctRank.canonicalBlockRankEntries true sparseBits sparseWs 1) sparseWs,
    sparseBits,
    tableBits (GenericSelect.sparseExceptionRelativeEntries b false)
      (GenericSelect.sparseExceptionRelativeWidth b) ]

/-- The eight interior tables of `canonicalRelativeRmmInteriorDirectory`, in
payload order: baseline, minRel, maxRel, argOffset, local sparse offsets,
global sparse blocks, local level table, global level table. -/
def interiorSegments (shape : CartesianShape) : List (List Bool) :=
  let L := SuccinctClose.RelativeRmm.canonicalLayout shape
  [ tableBits (SuccinctClose.bpSuperblockBaselineEntries shape L.blockSize L.blocksPerSuper
        L.superSampleCount) (L.superWidth shape),
    tableBits (SuccinctClose.bpBlockRelativeMinExcessEntries shape L.blockSize L.blocksPerSuper
        L.blockCount) L.relativeWidth,
    tableBits (SuccinctClose.bpBlockRelativeMaxExcessEntries shape L.blockSize L.blocksPerSuper
        L.blockCount) L.relativeWidth,
    tableBits (SuccinctClose.bpBlockArgMinLocalOffsetEntries shape L.blockSize L.blockCount)
      L.relativeWidth,
    tableBits (SuccinctClose.bpLocalSparseOffsetEntries shape L.blockSize L.blockCount
        L.macroSize L.macroSampleCount L.levelCount) L.offsetWidth,
    tableBits (SuccinctClose.bpGlobalSparseBlockEntries shape L.blockSize L.blockCount
        L.macroSize L.macroSampleCount L.globalLevelCount) L.blockAddressWidth,
    tableBits (SuccinctClose.bpSparseLevelEntries (SuccinctClose.bpSparseLevelDomain L.macroSize))
      (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain L.macroSize)),
    tableBits (SuccinctClose.bpSparseLevelEntries
        (SuccinctClose.bpSparseLevelDomain L.macroSampleCount))
      (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain L.macroSampleCount)) ]

/-- The fringe microtable at `c = bpFringeChunkBits (2n)`. -/
def fringeSegment (shape : CartesianShape) : List Bool :=
  let c := SuccinctClose.bpFringeChunkBits shape.bpCode.length
  tableBits (SuccinctClose.bpFringeChunkEntries c) (SuccinctClose.bpFringeChunkEntryWidth c)

/-- The select-chunk microtable (target `false`) at the same chunk width. -/
def selectChunkSegment (shape : CartesianShape) : List Bool :=
  let c := SuccinctClose.bpFringeChunkBits shape.bpCode.length
  tableBits (SuccinctClose.bpChunkSelectEntries c false) (SuccinctClose.bpChunkSelectEntryWidth c)

@[simp] theorem accessSegments_length (shape : CartesianShape) :
    (accessSegments shape).length = 18 := rfl

@[simp] theorem interiorSegments_length (shape : CartesianShape) :
    (interiorSegments shape).length = 8 := rfl

/-! ## Payload decomposition -/

theorem liveAccessPayload_eq_segments (shape : CartesianShape) :
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape =
      (accessSegments shape).flatten := by
  let SD := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let RD := builtRelativeSplitBPCloseRankData shape
  have h1 : RD.superTables.falseTable.payload = (accessSegments shape)[0] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h2 : RD.blockTables.falseTable.payload = (accessSegments shape)[1] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h3 : SD.superTable.baseOccurrenceTable.payload = (accessSegments shape)[2] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h4 : SD.superTable.baseWordIndexTable.payload = (accessSegments shape)[3] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h5 : SD.superTable.rankBeforeTable.payload = (accessSegments shape)[4] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h6 : SD.superTable.firstOffsetTable.payload = (accessSegments shape)[5] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h7 : SD.localTable.baseOccurrenceTable.payload = (accessSegments shape)[6] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h8 : SD.localTable.baseWordIndexTable.payload = (accessSegments shape)[7] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h9 : SD.localTable.rankBeforeTable.payload = (accessSegments shape)[8] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h10 : SD.localTable.firstOffsetTable.payload = (accessSegments shape)[9] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h11 : SD.longFlagRankData.superTables.trueTable.payload = (accessSegments shape)[10] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h12 : SD.longFlagRankData.blockTables.trueTable.payload = (accessSegments shape)[11] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h13 : SD.longFlagBits = (accessSegments shape)[12] := rfl
  have h14 : SD.longSuperRelativeTable.payload = (accessSegments shape)[13] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h15 : SD.sparseDirectory.rankData.superTables.trueTable.payload =
      (accessSegments shape)[14] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h16 : SD.sparseDirectory.rankData.blockTables.trueTable.payload =
      (accessSegments shape)[15] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have h17 : SD.sparseDirectory.flagBits = (accessSegments shape)[16] := rfl
  have h18 : SD.sparseDirectory.relativeTable.payload = (accessSegments shape)[17] :=
    FixedWidthNatTable.payload_eq_tableBits _
  have hlist : accessSegments shape =
      [RD.superTables.falseTable.payload, RD.blockTables.falseTable.payload,
        SD.superTable.baseOccurrenceTable.payload, SD.superTable.baseWordIndexTable.payload,
        SD.superTable.rankBeforeTable.payload, SD.superTable.firstOffsetTable.payload,
        SD.localTable.baseOccurrenceTable.payload, SD.localTable.baseWordIndexTable.payload,
        SD.localTable.rankBeforeTable.payload, SD.localTable.firstOffsetTable.payload,
        SD.longFlagRankData.superTables.trueTable.payload,
        SD.longFlagRankData.blockTables.trueTable.payload,
        SD.longFlagBits, SD.longSuperRelativeTable.payload,
        SD.sparseDirectory.rankData.superTables.trueTable.payload,
        SD.sparseDirectory.rankData.blockTables.trueTable.payload,
        SD.sparseDirectory.flagBits, SD.sparseDirectory.relativeTable.payload] := by
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
    rfl
  rw [hlist]
  rfl

theorem interiorPayload_eq_segments (shape : CartesianShape) :
    (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload =
      (interiorSegments shape).flatten := by
  have h1 : (SuccinctClose.canonicalRelativeRmmSummaryTable shape).baselineTable.payload =
      (interiorSegments shape)[0] := FixedWidthNatTable.payload_eq_tableBits _
  have h2 : (SuccinctClose.canonicalRelativeRmmSummaryTable shape).minRelTable.payload =
      (interiorSegments shape)[1] := FixedWidthNatTable.payload_eq_tableBits _
  have h3 : (SuccinctClose.canonicalRelativeRmmSummaryTable shape).maxRelTable.payload =
      (interiorSegments shape)[2] := FixedWidthNatTable.payload_eq_tableBits _
  have h4 : (SuccinctClose.canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload =
      (interiorSegments shape)[3] := FixedWidthNatTable.payload_eq_tableBits _
  have h5 : (SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape).table.payload =
      (interiorSegments shape)[4] := FixedWidthNatTable.payload_eq_tableBits _
  have h6 : (SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape).table.payload =
      (interiorSegments shape)[5] := FixedWidthNatTable.payload_eq_tableBits _
  have h7 : (SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload =
      (interiorSegments shape)[6] := FixedWidthNatTable.payload_eq_tableBits _
  have h8 : (SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload =
      (interiorSegments shape)[7] := FixedWidthNatTable.payload_eq_tableBits _
  have hlist : interiorSegments shape =
      [(SuccinctClose.canonicalRelativeRmmSummaryTable shape).baselineTable.payload,
        (SuccinctClose.canonicalRelativeRmmSummaryTable shape).minRelTable.payload,
        (SuccinctClose.canonicalRelativeRmmSummaryTable shape).maxRelTable.payload,
        (SuccinctClose.canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload,
        (SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape).table.payload,
        (SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape).table.payload,
        (SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload,
        (SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload] := by
    rw [h1, h2, h3, h4, h5, h6, h7, h8]
    rfl
  rw [hlist]
  show ((SuccinctClose.canonicalRelativeRmmSummaryTable shape).baselineTable.payload ++
      (SuccinctClose.canonicalRelativeRmmSummaryTable shape).minRelTable.payload ++
      (SuccinctClose.canonicalRelativeRmmSummaryTable shape).maxRelTable.payload ++
      (SuccinctClose.canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload) ++
      (SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape).table.payload ++
      (SuccinctClose.canonicalRelativeRmmInteriorGlobalTable shape).table.payload ++
      (SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
      (SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload = _
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- **Payload plan.** The canonical reviewer payload (= `packedReviewerPayloadBits`)
is the BP code, then the 18 access segments, the eight interior tables, the
fringe microtable and the select-chunk microtable, in this order. -/
theorem canonicalReviewerPayload_eq_plan (shape : CartesianShape) :
    packedReviewerPayloadBits shape =
      shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++
        fringeSegment shape ++ selectChunkSegment shape := by
  have hf : (SuccinctClose.bpFringeChunkTable
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).payload = fringeSegment shape :=
    FixedWidthNatTable.payload_eq_tableBits _
  have hs : (SuccinctClose.bpChunkSelectTable
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).payload =
      selectChunkSegment shape :=
    FixedWidthNatTable.payload_eq_tableBits _
  rw [← liveAccessPayload_eq_segments, ← interiorPayload_eq_segments, ← hf, ← hs]
  rfl

/-! ## Metadata as a function of three scalars -/

/-- The 42 scalar metadata words with the shape abstracted to `n`, `lc`, `sc`
(same fields, same order as `PackedWordRAM.scalarMetadata`). -/
def scalarMetadataOf (n lc sc : Nat) : List Nat :=
  let oldCount := packedReviewerCellCount n lc sc
  let oldBits := oldCount * packedReviewerCellWidth n
  let layout := packedInteriorLayout n
  let offsets := packedInteriorOffsets n
  let ld := SuccinctClose.bpSparseLevelDomain layout.macroSize
  let gd := SuccinctClose.bpSparseLevelDomain layout.macroSampleCount
  [n, packedReviewerCellWidth n, oldCount, oldBits, lc, sc,
    wordWidth n, metadataWordCount + GenericSelect.selectCeilDiv oldBits (wordWidth n),
    packedSelectWordSize n, packedSelectSuperStride n, packedSelectLocalStride n,
    packedSelectLocalSlotsPerSuper n, packedSuperSlots n, packedSparseSlots n,
    packedLongFlagWordSize n, packedSparseWordSize n,
    packedBpCodeWordWidth n, layout.blockSize, packedFringeChunkBits n,
    layout.blocksPerSuper, layout.blockCount, layout.superSampleCount,
    layout.macroSize, layout.macroSampleCount, layout.levelCount, layout.globalLevelCount,
    layout.relativeWidth, layout.offsetWidth, layout.blockAddressWidth, ld, gd,
    SuccinctClose.bpSparseLevelWidth ld, SuccinctClose.bpSparseLevelWidth gd,
    offsets.baseline, offsets.minRel, offsets.maxRel, offsets.argOffset,
    offsets.localOffset, offsets.globalBlock, offsets.localLevel, offsets.globalLevel,
    packedInteriorComponentWords n]

/-- The 174 metadata words as a function of `n`, `lc`, `sc`: 42 scalars, 23
four-word regular descriptors, eight five-word interior descriptors. -/
def metadataOf (n lc sc : Nat) : List Nat :=
  scalarMetadataOf n lc sc ++ ((List.range 23).map (regularDescriptor n lc sc)).flatten ++
    (interiorComponents.map (interiorDescriptor n lc sc)).flatten

/-- The metadata of a shape depends on it only through `n`, `lc` and `sc`. -/
theorem metadata_eq_metadataOf (shape : CartesianShape) :
    metadata shape =
      metadataOf shape.size (longCount shape) (packedReviewerSparseCount shape) := rfl

/-- The plan's name for `metadata_eq_metadataOf`. -/
theorem metadataOf_eq (shape : CartesianShape) :
    metadata shape =
      metadataOf shape.size (longCount shape) (packedReviewerSparseCount shape) :=
  metadata_eq_metadataOf shape

theorem metadataOf_length (n lc sc : Nat) : (metadataOf n lc sc).length = 174 := by
  have hregular := fixedMap_flatten_length (List.range 23) (regularDescriptor n lc sc) 4
    (by intro segment _; exact regularDescriptor_length ..)
  have hinterior := fixedMap_flatten_length interiorComponents (interiorDescriptor n lc sc) 5
    (by intro component _; exact interiorDescriptor_length ..)
  have hscalar : (scalarMetadataOf n lc sc).length = 42 := rfl
  simp only [metadataOf, List.length_append, hscalar, hregular, hinterior, List.length_range]
  rfl

/-! ## The old bit string -/

/-- The old serialized bit string with its first zero padding, as an explicit
emission order: header, BP, 18 access segments, eight interior tables, fringe,
select chunk, zeros up to `cellCount * oldW`. -/
def oldBitsPlan (shape : CartesianShape) : List Bool :=
  let n := shape.size
  let lc := longCount shape
  let sc := packedReviewerSparseCount shape
  let oldW := packedReviewerCellWidth n
  natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
    (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
    List.replicate
      (packedReviewerCellCount n lc sc * oldW - (oldW + packedReviewerPayloadLength n lc sc))
      false

/-- Length law for the payload plan (the measured-cursor target of the builder). -/
theorem planPayload_length (shape : CartesianShape) :
    (shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++
        fringeSegment shape ++ selectChunkSegment shape).length =
      packedReviewerPayloadLength shape.size (longCount shape) (packedReviewerSparseCount shape) := by
  rw [← canonicalReviewerPayload_eq_plan, packedReviewerPayloadBits_length_eq]

theorem packedReviewerPaddedBits_eq_plan (shape : CartesianShape) :
    packedReviewerPaddedBits shape = oldBitsPlan shape := by
  unfold packedReviewerPaddedBits oldBitsPlan
  rw [packedReviewerSerializedBits_length]
  unfold packedReviewerSerializedBits packedReviewerAllocatedBits packedReviewerHeaderBits
  rw [canonicalReviewerPayload_eq_plan]
  simp only [List.append_assoc]

theorem oldBitsPlan_length (shape : CartesianShape) :
    (oldBitsPlan shape).length =
      packedReviewerCellCount shape.size (longCount shape) (packedReviewerSparseCount shape) *
        packedReviewerCellWidth shape.size := by
  rw [← packedReviewerPaddedBits_eq_plan, packedReviewerPaddedBits_length]
  rfl


/-! ## The emission plan of the whole allocation -/

/-- **Plan, shape form.** -/
theorem shapeMemory_eq_plan (shape : CartesianShape) :
    let n := shape.size
    let lc := longCount shape
    let sc := packedReviewerSparseCount shape
    let W := wordWidth n
    let oldBits := packedReviewerCellCount n lc sc * packedReviewerCellWidth n
    let count := GenericSelect.selectCeilDiv oldBits W
    shapeMemory shape = metadataOf n lc sc ++
      (List.range count).map fun i =>
        bitsToNatLE (cellAt (oldBitsPlan shape ++ List.replicate (count * W - oldBits) false) W i) := by
  intro n lc sc W oldBits count
  unfold shapeMemory repackWords
  rw [metadata_eq_metadataOf, PackedCellProbe.packedReviewerMemory_flatten,
    packedReviewerPaddedBits_eq_plan]
  unfold denseWords denseCells densePad denseCount
  rw [oldBitsPlan_length, List.map_map]
  rfl

/-- Plan with the node count supplied through an equation, so the size-only
quantities can be stated at any expression equal to `shape.size`. -/
theorem shapeMemory_eq_plan_of_size (shape : CartesianShape) (n : Nat) (hn : shape.size = n) :
    let lc := longCount shape
    let sc := packedReviewerSparseCount shape
    let oldW := packedReviewerCellWidth n
    let W := wordWidth n
    let oldBits := packedReviewerCellCount n lc sc * oldW
    let count := GenericSelect.selectCeilDiv oldBits W
    let body :=
      natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
        (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
        List.replicate (oldBits - (oldW + packedReviewerPayloadLength n lc sc)) false
    shapeMemory shape = metadataOf n lc sc ++
      (List.range count).map fun i =>
        bitsToNatLE (cellAt (body ++ List.replicate (count * W - oldBits) false) W i) := by
  subst hn
  exact shapeMemory_eq_plan shape

/-- **`buildMemory_eq_plan`.** For every `xs : List Int`, `buildMemory xs` is
exactly: the 174 metadata words `metadataOf n lc sc`, then the dense repacking at
`W = wordWidth n` of the old bit string
`header ++ BP ++ 18 access segments ++ 8 interior tables ++ fringe ++ select chunk ++ pad₁`,
extended by the second zero padding `pad₂`, one word per `W` bits. -/
theorem buildMemory_eq_plan (xs : List Int) :
    let shape := SuccinctClassic.cartesianShape xs
    let n := xs.length
    let lc := longCount shape
    let sc := packedReviewerSparseCount shape
    let oldW := packedReviewerCellWidth n
    let W := wordWidth n
    let oldBits := packedReviewerCellCount n lc sc * oldW
    let count := GenericSelect.selectCeilDiv oldBits W
    let body :=
      natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
        (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
        List.replicate (oldBits - (oldW + packedReviewerPayloadLength n lc sc)) false
    buildMemory xs = metadataOf n lc sc ++
      (List.range count).map fun i =>
        bitsToNatLE (cellAt (body ++ List.replicate (count * W - oldBits) false) W i) :=
  shapeMemory_eq_plan_of_size (SuccinctClassic.cartesianShape xs) xs.length
    (packedReviewerCartesianShape_size xs)

theorem oldBitsPlan_length_of_size (shape : CartesianShape) (n : Nat) (hn : shape.size = n) :
    let lc := longCount shape
    let sc := packedReviewerSparseCount shape
    let oldW := packedReviewerCellWidth n
    (natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
        (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
        List.replicate (packedReviewerCellCount n lc sc * oldW -
          (oldW + packedReviewerPayloadLength n lc sc)) false).length =
      packedReviewerCellCount n lc sc * oldW := by
  subst hn
  exact oldBitsPlan_length shape

/-- The old bit string of the plan fills exactly `cellCount * oldW` bits. -/
theorem buildMemory_plan_body_length (xs : List Int) :
    let shape := SuccinctClassic.cartesianShape xs
    let n := xs.length
    let lc := longCount shape
    let sc := packedReviewerSparseCount shape
    let oldW := packedReviewerCellWidth n
    (natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
        (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
        List.replicate (packedReviewerCellCount n lc sc * oldW -
          (oldW + packedReviewerPayloadLength n lc sc)) false).length =
      packedReviewerCellCount n lc sc * oldW :=
  oldBitsPlan_length_of_size (SuccinctClassic.cartesianShape xs) xs.length
    (packedReviewerCartesianShape_size xs)

end RMQ.SuccinctFinal.PackedConstruction.Spec

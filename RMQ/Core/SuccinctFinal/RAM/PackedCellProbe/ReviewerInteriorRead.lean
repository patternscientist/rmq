import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerProbe
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram

/-!
# Physical lowering for the ragged interior component store

Segment `20` is an append of eight independently chunked fixed-width tables.
Consequently its machine-word boundaries are not the boundaries obtained by
chunking the concatenated directory payload.  This module keeps the component
identity and the entry-local chunk coordinates explicit all the way to the
reviewer-memory request.

The executable geometry below is first-order and depends only on `n` and the
logical segment-local word index.  In particular, it contains no shape, table,
store, source program, semantic answer, or proof value.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace
open RMQ.SuccinctClose

/-! ## Closed first-order component geometry -/

/-- The eight physical components, in their exact segment-20 word order. -/
inductive PackedReviewerInteriorComponentTag where
  | baseline
  | minRel
  | maxRel
  | argOffset
  | localOffset
  | globalBlock
  | localLevel
  | globalLevel
deriving DecidableEq, Repr

/-- Entry count of one component, computed from the public input size alone. -/
def packedReviewerInteriorEntryCount
    (n : Nat) (component : PackedReviewerInteriorComponentTag) : Nat :=
  let layout := packedInteriorLayout n
  match component with
  | .baseline => layout.superSampleCount
  | .minRel | .maxRel | .argOffset => layout.blockCount
  | .localOffset => layout.macroSampleCount * (layout.levelCount * layout.macroSize)
  | .globalBlock => layout.globalLevelCount * layout.macroSampleCount
  | .localLevel => bpSparseLevelDomain layout.macroSize
  | .globalLevel => bpSparseLevelDomain layout.macroSampleCount

/-- Fixed entry width of one component, computed from `n` alone. -/
def packedReviewerInteriorEntryWidth
    (n : Nat) (component : PackedReviewerInteriorComponentTag) : Nat :=
  let layout := packedInteriorLayout n
  match component with
  | .baseline => packedBpCodeWordWidth n
  | .minRel | .maxRel | .argOffset => layout.relativeWidth
  | .localOffset => layout.offsetWidth
  | .globalBlock => layout.blockAddressWidth
  | .localLevel => bpSparseLevelWidth (bpSparseLevelDomain layout.macroSize)
  | .globalLevel => bpSparseLevelWidth (bpSparseLevelDomain layout.macroSampleCount)

/-- Machine-word count of one component. -/
def packedReviewerInteriorComponentWordCount
    (n : Nat) (component : PackedReviewerInteriorComponentTag) : Nat :=
  packedInteriorTableWords
    (packedReviewerInteriorEntryCount n component)
    (packedReviewerInteriorEntryWidth n component)
    (packedBpCodeWordWidth n)

theorem packedReviewerInteriorComponentWordCount_eq
    (n : Nat) (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentWordCount n component =
      match component with
      | .baseline => packedBaselineWords n
      | .minRel => packedMinRelWords n
      | .maxRel => packedMaxRelWords n
      | .argOffset => packedArgOffsetWords n
      | .localOffset => packedLocalTableWords n
      | .globalBlock => packedGlobalTableWords n
      | .localLevel => packedLocalLevelWords n
      | .globalLevel => packedGlobalLevelWords n := by
  cases component <;> rfl

/-- Closed table-word geometry is entry count times chunks per entry. -/
theorem packedReviewerInteriorTableWords_eq_chunkCount
    (entryCount width wordSize : Nat) (hword : 0 < wordSize) :
  packedInteriorTableWords entryCount width wordSize =
      entryCount * packedChunkCount width wordSize := by
  unfold packedInteriorTableWords packedChunkCount
  rw [chunkPayloadWords_length_eq_div_add_indicator hword
        (List.replicate width false),
    List.length_replicate]

/-- Segment-local word offset of one component. -/
def packedReviewerInteriorComponentWordPrefix
    (n : Nat) (component : PackedReviewerInteriorComponentTag) : Nat :=
  let offsets := packedInteriorOffsets n
  match component with
  | .baseline => offsets.baseline
  | .minRel => offsets.minRel
  | .maxRel => offsets.maxRel
  | .argOffset => offsets.argOffset
  | .localOffset => offsets.localOffset
  | .globalBlock => offsets.globalBlock
  | .localLevel => offsets.localLevel
  | .globalLevel => offsets.globalLevel

/-- Number of directory payload bits preceding one component. -/
def packedReviewerInteriorComponentBitPrefix
    (n : Nat) (component : PackedReviewerInteriorComponentTag) : Nat :=
  let bits (c : PackedReviewerInteriorComponentTag) :=
    packedReviewerInteriorEntryCount n c * packedReviewerInteriorEntryWidth n c
  match component with
  | .baseline => 0
  | .minRel => bits .baseline
  | .maxRel => bits .baseline + bits .minRel
  | .argOffset => bits .baseline + bits .minRel + bits .maxRel
  | .localOffset => bits .baseline + bits .minRel + bits .maxRel + bits .argOffset
  | .globalBlock =>
      bits .baseline + bits .minRel + bits .maxRel + bits .argOffset +
        bits .localOffset
  | .localLevel =>
      bits .baseline + bits .minRel + bits .maxRel + bits .argOffset +
        bits .localOffset + bits .globalBlock
  | .globalLevel =>
      bits .baseline + bits .minRel + bits .maxRel + bits .argOffset +
        bits .localOffset + bits .globalBlock + bits .localLevel

/--
Proof-free geometry for one segment-20 word.  `bitOffset` is relative to the
component payload; `componentBitPrefix + bitOffset` is its directory offset.
-/
structure PackedReviewerInteriorLocation where
  component : PackedReviewerInteriorComponentTag
  localWordIndex : Nat
  entryIndex : Nat
  chunkIndex : Nat
  componentBitPrefix : Nat
  bitOffset : Nat
  readWidth : Nat
deriving DecidableEq, Repr

/-- Build the full two-level entry/chunk geometry for a component-local word. -/
def packedReviewerInteriorLocation
    (n : Nat) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat) : PackedReviewerInteriorLocation :=
  let width := packedReviewerInteriorEntryWidth n component
  let wordSize := packedBpCodeWordWidth n
  let chunks := packedChunkCount width wordSize
  { component
    localWordIndex
    entryIndex := localWordIndex / chunks
    chunkIndex := localWordIndex % chunks
    componentBitPrefix := packedReviewerInteriorComponentBitPrefix n component
    bitOffset := packedEntryChunkBitOffset width wordSize localWordIndex
    readWidth := packedEntryChunkReadWidth width wordSize localWordIndex }

/-- Exact entry/chunk coordinates, including the short final chunk width. -/
theorem packedReviewerInteriorLocation_coordinates
    (n : Nat) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat) :
    let location := packedReviewerInteriorLocation n component localWordIndex
    let width := packedReviewerInteriorEntryWidth n component
    let wordSize := packedBpCodeWordWidth n
    let chunks := packedChunkCount width wordSize
    location.component = component /\
      location.localWordIndex = localWordIndex /\
      location.entryIndex = localWordIndex / chunks /\
      location.chunkIndex = localWordIndex % chunks /\
      location.componentBitPrefix =
        packedReviewerInteriorComponentBitPrefix n component /\
      location.bitOffset = location.chunkIndex * wordSize +
        location.entryIndex * width /\
      location.readWidth =
        min (width - location.chunkIndex * wordSize) wordSize := by
  simp [packedReviewerInteriorLocation, packedEntryChunkBitOffset,
    packedEntryChunkReadWidth]

/--
Classify a segment-local word index by the size-only component offsets.  The
subtractions are the component-local word positions; an index at or beyond the
dead address classifies as `none`.
-/
def packedReviewerInteriorClassify
    (n index : Nat) : Option PackedReviewerInteriorLocation :=
  let offsets := packedInteriorOffsets n
  if index < offsets.minRel then
    some (packedReviewerInteriorLocation n .baseline index)
  else if index < offsets.maxRel then
    some (packedReviewerInteriorLocation n .minRel (index - offsets.minRel))
  else if index < offsets.argOffset then
    some (packedReviewerInteriorLocation n .maxRel (index - offsets.maxRel))
  else if index < offsets.localOffset then
    some (packedReviewerInteriorLocation n .argOffset (index - offsets.argOffset))
  else if index < offsets.globalBlock then
    some (packedReviewerInteriorLocation n .localOffset (index - offsets.localOffset))
  else if index < offsets.localLevel then
    some (packedReviewerInteriorLocation n .globalBlock (index - offsets.globalBlock))
  else if index < offsets.globalLevel then
    some (packedReviewerInteriorLocation n .localLevel (index - offsets.localLevel))
  else if index < packedInteriorComponentWords n then
    some (packedReviewerInteriorLocation n .globalLevel (index - offsets.globalLevel))
  else
    none

theorem packedReviewerInteriorClassify_eq_none_iff (n index : Nat) :
    packedReviewerInteriorClassify n index = none ↔
      packedInteriorComponentWords n <= index := by
  by_cases hbaseline : index < (packedInteriorOffsets n).minRel
  · simp [packedReviewerInteriorClassify, hbaseline]
    simp only [packedInteriorOffsets] at *
    unfold packedInteriorComponentWords at *
    omega
  · by_cases hminRel : index < (packedInteriorOffsets n).maxRel
    · simp [packedReviewerInteriorClassify, hbaseline, hminRel]
      simp only [packedInteriorOffsets] at *
      unfold packedInteriorComponentWords at *
      omega
    · by_cases hmaxRel : index < (packedInteriorOffsets n).argOffset
      · simp [packedReviewerInteriorClassify, hbaseline, hminRel, hmaxRel]
        simp only [packedInteriorOffsets] at *
        unfold packedInteriorComponentWords at *
        omega
      · by_cases hargOffset : index < (packedInteriorOffsets n).localOffset
        · simp [packedReviewerInteriorClassify, hbaseline, hminRel, hmaxRel,
            hargOffset]
          simp only [packedInteriorOffsets] at *
          unfold packedInteriorComponentWords at *
          omega
        · by_cases hlocalOffset : index < (packedInteriorOffsets n).globalBlock
          · simp [packedReviewerInteriorClassify, hbaseline, hminRel, hmaxRel,
              hargOffset, hlocalOffset]
            simp only [packedInteriorOffsets] at *
            unfold packedInteriorComponentWords at *
            omega
          · by_cases hglobalBlock : index < (packedInteriorOffsets n).localLevel
            · simp [packedReviewerInteriorClassify, hbaseline, hminRel, hmaxRel,
                hargOffset, hlocalOffset, hglobalBlock]
              simp only [packedInteriorOffsets] at *
              unfold packedInteriorComponentWords at *
              omega
            · by_cases hlocalLevel : index < (packedInteriorOffsets n).globalLevel
              · simp [packedReviewerInteriorClassify, hbaseline, hminRel, hmaxRel,
                  hargOffset, hlocalOffset, hglobalBlock, hlocalLevel]
                simp only [packedInteriorOffsets] at *
                unfold packedInteriorComponentWords at *
                omega
              · by_cases hglobalLevel : index < packedInteriorComponentWords n
                · simp [packedReviewerInteriorClassify, hbaseline, hminRel,
                    hmaxRel, hargOffset, hlocalOffset, hglobalBlock, hlocalLevel,
                    hglobalLevel]
                · simp [packedReviewerInteriorClassify, hbaseline, hminRel,
                    hmaxRel, hargOffset, hlocalOffset, hglobalBlock, hlocalLevel,
                    hglobalLevel]
                  omega

/-- The exact first out-of-range word has no component. -/
theorem packedReviewerInteriorClassify_deadAddress (n : Nat) :
    packedReviewerInteriorClassify n (packedInteriorComponentWords n) = none :=
  (packedReviewerInteriorClassify_eq_none_iff _ _).2 (Nat.le_refl _)

/--
The classifier retains the original position and puts it in exactly one
component.  This is the arithmetic receipt consumed by the ordered lowering.
-/
theorem packedReviewerInteriorClassify_sound
    {n index : Nat} {location : PackedReviewerInteriorLocation}
    (hclassify : packedReviewerInteriorClassify n index = some location) :
    location = packedReviewerInteriorLocation n location.component
        location.localWordIndex /\
      index = packedReviewerInteriorComponentWordPrefix n location.component +
        location.localWordIndex /\
      location.localWordIndex <
        packedReviewerInteriorComponentWordCount n location.component := by
  unfold packedReviewerInteriorClassify at hclassify
  dsimp only at hclassify
  by_cases hbaseline : index < (packedInteriorOffsets n).minRel
  · simp [hbaseline] at hclassify
    subst location
    change index < packedBaselineWords n at hbaseline
    refine ⟨rfl, ?_, ?_⟩
    · simp [packedReviewerInteriorLocation,
        packedReviewerInteriorComponentWordPrefix, packedInteriorOffsets]
    · simp only [packedReviewerInteriorLocation]
      rw [packedReviewerInteriorComponentWordCount_eq]
      simpa [packedInteriorOffsets] using hbaseline
  · simp [hbaseline] at hclassify
    by_cases hminRel : index < (packedInteriorOffsets n).maxRel
    · simp [hminRel] at hclassify
      subst location
      change ¬index < packedBaselineWords n at hbaseline
      change index < packedBaselineWords n + packedMinRelWords n at hminRel
      refine ⟨rfl, ?_, ?_⟩
      · simp only [packedReviewerInteriorLocation,
          packedReviewerInteriorComponentWordPrefix,
          packedInteriorOffsets]
        omega
      · simp only [packedReviewerInteriorLocation]
        rw [packedReviewerInteriorComponentWordCount_eq]
        simp [packedInteriorOffsets] at *
        omega
    · simp [hminRel] at hclassify
      by_cases hmaxRel : index < (packedInteriorOffsets n).argOffset
      · simp [hmaxRel] at hclassify
        subst location
        change ¬index < packedBaselineWords n + packedMinRelWords n at hminRel
        change index < packedBaselineWords n + packedMinRelWords n +
          packedMaxRelWords n at hmaxRel
        refine ⟨rfl, ?_, ?_⟩
        · simp only [packedReviewerInteriorLocation,
            packedReviewerInteriorComponentWordPrefix,
            packedInteriorOffsets]
          omega
        · simp only [packedReviewerInteriorLocation]
          rw [packedReviewerInteriorComponentWordCount_eq]
          simp [packedInteriorOffsets] at *
          omega
      · simp [hmaxRel] at hclassify
        by_cases hargOffset : index < (packedInteriorOffsets n).localOffset
        · simp [hargOffset] at hclassify
          subst location
          change ¬index < packedBaselineWords n + packedMinRelWords n +
            packedMaxRelWords n at hmaxRel
          change index < packedBaselineWords n + packedMinRelWords n +
            packedMaxRelWords n + packedArgOffsetWords n at hargOffset
          refine ⟨rfl, ?_, ?_⟩
          · simp only [packedReviewerInteriorLocation,
              packedReviewerInteriorComponentWordPrefix,
              packedInteriorOffsets]
            omega
          · simp only [packedReviewerInteriorLocation]
            rw [packedReviewerInteriorComponentWordCount_eq]
            simp [packedInteriorOffsets] at *
            omega
        · simp [hargOffset] at hclassify
          by_cases hlocalOffset : index < (packedInteriorOffsets n).globalBlock
          · simp [hlocalOffset] at hclassify
            subst location
            change ¬index < packedBaselineWords n + packedMinRelWords n +
              packedMaxRelWords n + packedArgOffsetWords n at hargOffset
            change index < packedBaselineWords n + packedMinRelWords n +
              packedMaxRelWords n + packedArgOffsetWords n +
                packedLocalTableWords n at hlocalOffset
            refine ⟨rfl, ?_, ?_⟩
            · simp only [packedReviewerInteriorLocation,
                packedReviewerInteriorComponentWordPrefix,
                packedInteriorOffsets]
              omega
            · simp only [packedReviewerInteriorLocation]
              rw [packedReviewerInteriorComponentWordCount_eq]
              simp [packedInteriorOffsets] at *
              omega
          · simp [hlocalOffset] at hclassify
            by_cases hglobalBlock : index < (packedInteriorOffsets n).localLevel
            · simp [hglobalBlock] at hclassify
              subst location
              change ¬index < packedBaselineWords n + packedMinRelWords n +
                packedMaxRelWords n + packedArgOffsetWords n +
                  packedLocalTableWords n at hlocalOffset
              change index < packedBaselineWords n + packedMinRelWords n +
                packedMaxRelWords n + packedArgOffsetWords n +
                  packedLocalTableWords n + packedGlobalTableWords n at hglobalBlock
              refine ⟨rfl, ?_, ?_⟩
              · simp only [packedReviewerInteriorLocation,
                  packedReviewerInteriorComponentWordPrefix,
                  packedInteriorOffsets]
                omega
              · simp only [packedReviewerInteriorLocation]
                rw [packedReviewerInteriorComponentWordCount_eq]
                simp [packedInteriorOffsets] at *
                omega
            · simp [hglobalBlock] at hclassify
              by_cases hlocalLevel : index < (packedInteriorOffsets n).globalLevel
              · simp [hlocalLevel] at hclassify
                subst location
                change ¬index < packedBaselineWords n + packedMinRelWords n +
                  packedMaxRelWords n + packedArgOffsetWords n +
                    packedLocalTableWords n + packedGlobalTableWords n at hglobalBlock
                change index < packedBaselineWords n + packedMinRelWords n +
                  packedMaxRelWords n + packedArgOffsetWords n +
                    packedLocalTableWords n + packedGlobalTableWords n +
                      packedLocalLevelWords n at hlocalLevel
                refine ⟨rfl, ?_, ?_⟩
                · simp only [packedReviewerInteriorLocation,
                    packedReviewerInteriorComponentWordPrefix,
                    packedInteriorOffsets]
                  omega
                · simp only [packedReviewerInteriorLocation]
                  rw [packedReviewerInteriorComponentWordCount_eq]
                  simp [packedInteriorOffsets] at *
                  omega
              · simp [hlocalLevel] at hclassify
                by_cases hglobalLevel : index < packedInteriorComponentWords n
                · simp [hglobalLevel] at hclassify
                  subst location
                  change ¬index < packedBaselineWords n + packedMinRelWords n +
                    packedMaxRelWords n + packedArgOffsetWords n +
                      packedLocalTableWords n + packedGlobalTableWords n +
                        packedLocalLevelWords n at hlocalLevel
                  unfold packedInteriorComponentWords at hglobalLevel
                  refine ⟨rfl, ?_, ?_⟩
                  · simp only [packedReviewerInteriorLocation,
                      packedReviewerInteriorComponentWordPrefix,
                      packedInteriorOffsets]
                    omega
                  · simp only [packedReviewerInteriorLocation]
                    rw [packedReviewerInteriorComponentWordCount_eq]
                    simp [packedInteriorOffsets] at *
                    omega
                · simp [hglobalLevel] at hclassify

/-! ## Canonical shape-facing objects used only in correctness proofs -/

/-- The canonical component payload selected by the closed tag. -/
def packedReviewerInteriorCanonicalPayload
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    List Bool :=
  match component with
  | .baseline => (canonicalRelativeRmmSummaryTable shape).baselineTable.payload
  | .minRel => (canonicalRelativeRmmSummaryTable shape).minRelTable.payload
  | .maxRel => (canonicalRelativeRmmSummaryTable shape).maxRelTable.payload
  | .argOffset => (canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload
  | .localOffset => (canonicalRelativeRmmInteriorLocalTable shape).table.payload
  | .globalBlock => (canonicalRelativeRmmInteriorGlobalTable shape).table.payload
  | .localLevel => (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload
  | .globalLevel => (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload

/-- The canonical machine words selected by the closed tag. -/
def packedReviewerInteriorCanonicalWords
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    List (List Bool) :=
  match component with
  | .baseline => packedInteriorBaselineWords shape
  | .minRel => packedInteriorMinRelWords shape
  | .maxRel => packedInteriorMaxRelWords shape
  | .argOffset => packedInteriorArgOffsetWords shape
  | .localOffset => packedInteriorLocalWords shape
  | .globalBlock => packedInteriorGlobalWords shape
  | .localLevel => packedInteriorLocalLevelWords shape
  | .globalLevel => packedInteriorGlobalLevelWords shape

/-- The payload prefix preceding the selected component. -/
def packedReviewerInteriorCanonicalPayloadPrefix
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    List Bool :=
  let payload := packedReviewerInteriorCanonicalPayload shape
  match component with
  | .baseline => []
  | .minRel => payload .baseline
  | .maxRel => payload .baseline ++ payload .minRel
  | .argOffset => payload .baseline ++ payload .minRel ++ payload .maxRel
  | .localOffset =>
      payload .baseline ++ payload .minRel ++ payload .maxRel ++ payload .argOffset
  | .globalBlock =>
      payload .baseline ++ payload .minRel ++ payload .maxRel ++ payload .argOffset ++
        payload .localOffset
  | .localLevel =>
      payload .baseline ++ payload .minRel ++ payload .maxRel ++ payload .argOffset ++
        payload .localOffset ++ payload .globalBlock
  | .globalLevel =>
      payload .baseline ++ payload .minRel ++ payload .maxRel ++ payload .argOffset ++
        payload .localOffset ++ payload .globalBlock ++ payload .localLevel

/-- The payload geometry of every canonical component matches the `n`-only one. -/
theorem packedReviewerInteriorCanonicalPayload_length
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    (packedReviewerInteriorCanonicalPayload shape component).length =
      packedReviewerInteriorEntryCount shape.size component *
        packedReviewerInteriorEntryWidth shape.size component := by
  cases component <;> simp only [packedReviewerInteriorCanonicalPayload]
  · rw [(canonicalRelativeRmmSummaryTable shape).baselineTable.payload_length_eq,
      bpSuperblockBaselineEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq, packedBpCodeWordWidth,
      RelativeRmm.Layout.superWidth,
      CartesianShape.bpCode_length]
  · rw [(canonicalRelativeRmmSummaryTable shape).minRelTable.payload_length_eq,
      bpBlockRelativeMinExcessEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]
  · rw [(canonicalRelativeRmmSummaryTable shape).maxRelTable.payload_length_eq,
      bpBlockRelativeMaxExcessEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]
  · rw [(canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload_length_eq,
      bpBlockArgMinLocalOffsetEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]
  · rw [(canonicalRelativeRmmInteriorLocalTable shape).table.payload_length_eq,
      bpLocalSparseOffsetEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]
  · rw [(canonicalRelativeRmmInteriorGlobalTable shape).table.payload_length_eq,
      bpGlobalSparseBlockEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]
  · rw [(canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload_length_eq,
      bpSparseLevelEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]
  · rw [(canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload_length_eq,
      bpSparseLevelEntries_length]
    simp [packedReviewerInteriorCanonicalPayload,
      packedReviewerInteriorEntryCount, packedReviewerInteriorEntryWidth,
      packedInteriorLayout_eq]

/-- The `n`-only bit prefix is exactly the canonical payload-prefix length. -/
theorem packedReviewerInteriorComponentBitPrefix_eq
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentBitPrefix shape.size component =
      (packedReviewerInteriorCanonicalPayloadPrefix shape component).length := by
  cases component <;>
    simp [packedReviewerInteriorComponentBitPrefix,
      packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload_length] <;> omega

/-- Canonical component word counts are exactly the closed `n`-only counts. -/
theorem packedReviewerInteriorCanonicalWords_length
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    (packedReviewerInteriorCanonicalWords shape component).length =
      packedReviewerInteriorComponentWordCount shape.size component := by
  cases component
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedBaselineWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedMinRelWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedMaxRelWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedArgOffsetWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedLocalTableWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedGlobalTableWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedLocalLevelWords_eq shape
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorComponentWordCount_eq] using packedGlobalLevelWords_eq shape

/-- Closed component word prefixes are the actual canonical append prefixes. -/
theorem packedReviewerInteriorComponentWordPrefix_eq
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    packedReviewerInteriorComponentWordPrefix shape.size component =
      match component with
      | .baseline => 0
      | .minRel => (packedInteriorBaselineWords shape).length
      | .maxRel =>
          (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape).length
      | .argOffset =>
          (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
            packedInteriorMaxRelWords shape).length
      | .localOffset =>
          (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
            packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape).length
      | .globalBlock =>
          (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
            packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape ++
              packedInteriorLocalWords shape).length
      | .localLevel =>
          (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
            packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape ++
              packedInteriorLocalWords shape ++ packedInteriorGlobalWords shape).length
      | .globalLevel =>
          (packedInteriorBaselineWords shape ++ packedInteriorMinRelWords shape ++
            packedInteriorMaxRelWords shape ++ packedInteriorArgOffsetWords shape ++
              packedInteriorLocalWords shape ++ packedInteriorGlobalWords shape ++
                packedInteriorLocalLevelWords shape).length := by
  cases component <;>
    simp only [packedReviewerInteriorComponentWordPrefix] <;>
    rw [← packedInteriorOffsets_eq shape] <;>
    simp only [packedInteriorOffsets_baseline, packedInteriorOffsets_minRel,
      packedInteriorOffsets_maxRel, packedInteriorOffsets_argOffset,
      packedInteriorOffsets_localOffset, packedInteriorOffsets_globalBlock,
      packedInteriorOffsets_localLevel, packedInteriorOffsets_globalLevel]

/-- A middle slice is unchanged by the payloads before and after it. -/
theorem packedReviewerInteriorMiddleSlice
    {α : Type} (before middle after : List α) {off len : Nat}
    (h : off + len <= middle.length) :
    (((before ++ middle ++ after).drop (before.length + off)).take len) =
      ((middle.drop off).take len) := by
  rw [show before ++ middle ++ after = before ++ (middle ++ after) by
    simp [List.append_assoc]]
  rw [← List.drop_drop, List.drop_left]
  exact packedPrefixSlice _ _ h

/-- The directory decomposes around every tagged component in exact order. -/
theorem packedReviewerInteriorDirectory_decompose
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    exists suffix,
      (canonicalRelativeRmmInteriorDirectory shape).payload =
        packedReviewerInteriorCanonicalPayloadPrefix shape component ++
          packedReviewerInteriorCanonicalPayload shape component ++ suffix := by
  rw [packedInteriorDirectoryPayload_split shape]
  cases component
  · refine ⟨
      (canonicalRelativeRmmSummaryTable shape).minRelTable.payload ++
        (canonicalRelativeRmmSummaryTable shape).maxRelTable.payload ++
          (canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload ++
            (canonicalRelativeRmmInteriorLocalTable shape).table.payload ++
              (canonicalRelativeRmmInteriorGlobalTable shape).table.payload ++
                (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
                  (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload,
      ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨
      (canonicalRelativeRmmSummaryTable shape).maxRelTable.payload ++
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload ++
          (canonicalRelativeRmmInteriorLocalTable shape).table.payload ++
            (canonicalRelativeRmmInteriorGlobalTable shape).table.payload ++
              (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
                (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload,
      ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable.payload ++
        (canonicalRelativeRmmInteriorLocalTable shape).table.payload ++
          (canonicalRelativeRmmInteriorGlobalTable shape).table.payload ++
            (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
              (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload,
      ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨
      (canonicalRelativeRmmInteriorLocalTable shape).table.payload ++
        (canonicalRelativeRmmInteriorGlobalTable shape).table.payload ++
          (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
            (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload,
      ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨
      (canonicalRelativeRmmInteriorGlobalTable shape).table.payload ++
        (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
          (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload,
      ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload ++
        (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload,
      ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload, ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]
  · refine ⟨[], ?_⟩
    simp [packedReviewerInteriorCanonicalPayloadPrefix,
      packedReviewerInteriorCanonicalPayload, List.append_assoc]

/--
Every component-local payload range is the corresponding range of the canonical
interior directory.  This is a bit-prefix theorem, not a word-prefix theorem.
-/
theorem packedReviewerInteriorDirectorySlice
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    {off len : Nat}
    (hfit : off + len <=
      (packedReviewerInteriorCanonicalPayload shape component).length) :
    (((canonicalRelativeRmmInteriorDirectory shape).payload.drop
        (packedReviewerInteriorComponentBitPrefix shape.size component + off)).take
      len) =
      ((packedReviewerInteriorCanonicalPayload shape component).drop off).take len := by
  obtain ⟨suffix, hdecompose⟩ :=
    packedReviewerInteriorDirectory_decompose shape component
  rw [hdecompose, packedReviewerInteriorComponentBitPrefix_eq shape component]
  exact packedReviewerInteriorMiddleSlice _ _ _ hfit

/-! ## Component-local word exactness and word-order preservation -/

/-- A local component word is its entry-local chunk, including a short last chunk. -/
theorem packedReviewerInteriorCanonicalWord
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    (packedReviewerInteriorCanonicalWords shape component)[localWordIndex]? =
      some (((packedReviewerInteriorCanonicalPayload shape component).drop
          (packedReviewerInteriorLocation shape.size component localWordIndex).bitOffset).take
        (packedReviewerInteriorLocation shape.size component localWordIndex).readWidth) := by
  cases component
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, RelativeRmm.Layout.superWidth,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmSummaryTable shape).baselineTable
          (packedInteriorSuperWidth_pos shape) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmSummaryTable shape).minRelTable
          (packedInteriorRelativeWidth_pos shape) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmSummaryTable shape).maxRelTable
          (packedInteriorRelativeWidth_pos shape) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmSummaryTable shape).argOffsetTable
          (packedInteriorRelativeWidth_pos shape) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmInteriorLocalTable shape).table
          (packedInteriorOffsetWidth_pos shape) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmInteriorGlobalTable shape).table
          (packedInteriorBlockAddressWidth_pos shape) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmInteriorLocalLevelTable shape).table
          (by unfold bpSparseLevelWidth; omega) localWordIndex hlocal
  · simpa [packedReviewerInteriorCanonicalWords,
      packedReviewerInteriorCanonicalPayload, packedReviewerInteriorLocation,
      packedReviewerInteriorEntryWidth, packedInteriorWordSize,
      packedBpCodeWordWidth, packedInteriorLayout_eq,
      CartesianShape.bpCode_length] using
        packedInteriorComponentWord_of_lt_size shape
          (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
          (by unfold bpSparseLevelWidth; omega) localWordIndex hlocal

/-- Every entry width used by the classifier is positive on a canonical shape. -/
theorem packedReviewerInteriorEntryWidth_pos
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag) :
    0 < packedReviewerInteriorEntryWidth shape.size component := by
  cases component
  · simpa [packedReviewerInteriorEntryWidth, packedInteriorLayout_eq,
      packedBpCodeWordWidth, RelativeRmm.Layout.superWidth,
      CartesianShape.bpCode_length] using packedInteriorSuperWidth_pos shape
  · simpa [packedReviewerInteriorEntryWidth, packedInteriorLayout_eq] using
      packedInteriorRelativeWidth_pos shape
  · simpa [packedReviewerInteriorEntryWidth, packedInteriorLayout_eq] using
      packedInteriorRelativeWidth_pos shape
  · simpa [packedReviewerInteriorEntryWidth, packedInteriorLayout_eq] using
      packedInteriorRelativeWidth_pos shape
  · simpa [packedReviewerInteriorEntryWidth, packedInteriorLayout_eq] using
      packedInteriorOffsetWidth_pos shape
  · simpa [packedReviewerInteriorEntryWidth, packedInteriorLayout_eq] using
      packedInteriorBlockAddressWidth_pos shape
  · simp [packedReviewerInteriorEntryWidth, bpSparseLevelWidth]
  · simp [packedReviewerInteriorEntryWidth, bpSparseLevelWidth]

/-- A local chunk begins before the end of its positive-width entry. -/
theorem packedReviewerInteriorChunkOffset_lt
    {width wordSize localWordIndex : Nat}
    (hwidth : 0 < width) (hword : 0 < wordSize) :
    (localWordIndex % packedChunkCount width wordSize) * wordSize < width := by
  have hdecompose := Nat.mod_add_div width wordSize
  rw [Nat.mul_comm wordSize (width / wordSize)] at hdecompose
  unfold packedChunkCount
  split
  · rename_i hrem
    have hwordLe : wordSize <= width := by
      apply Nat.le_of_not_gt
      intro hlt
      have hmodSelf := Nat.mod_eq_of_lt hlt
      omega
    have hquotient : 0 < width / wordSize := Nat.div_pos hwordLe hword
    have hmod : localWordIndex % (width / wordSize) < width / wordSize :=
      Nat.mod_lt _ hquotient
    have hmul := Nat.mul_lt_mul_of_pos_right hmod hword
    simp only [Nat.add_zero]
    omega
  · rename_i hrem
    have hremPos : 0 < width % wordSize := Nat.pos_of_ne_zero hrem
    have hdenom : 0 < width / wordSize + 1 := Nat.succ_pos _
    have hmod :
        localWordIndex % (width / wordSize + 1) < width / wordSize + 1 :=
      Nat.mod_lt _ hdenom
    have hmul := Nat.mul_le_mul_right wordSize
      (show localWordIndex % (width / wordSize + 1) <= width / wordSize by omega)
    omega

/--
The exact entry-local chunk range lies in the concatenated fixed-width payload.
This arithmetic is what makes the short final `min` width load-bearing.
-/
theorem packedReviewerInteriorEntryChunk_fits
    {entryCount width wordSize localWordIndex : Nat}
    (hwidth : 0 < width) (hword : 0 < wordSize)
    (hlocal : localWordIndex < entryCount * packedChunkCount width wordSize) :
    packedEntryChunkBitOffset width wordSize localWordIndex +
        packedEntryChunkReadWidth width wordSize localWordIndex <=
      entryCount * width := by
  have hc : 0 < packedChunkCount width wordSize :=
    packedChunkCount_pos hword hwidth
  have hentry : localWordIndex / packedChunkCount width wordSize < entryCount :=
    packedEntryIndex_lt_of_lt hc hlocal
  have hchunk :=
    packedReviewerInteriorChunkOffset_lt (localWordIndex := localWordIndex)
      hwidth hword
  have hmin :
      packedEntryChunkReadWidth width wordSize localWordIndex <=
        width -
          (localWordIndex % packedChunkCount width wordSize) * wordSize := by
    exact Nat.min_le_left _ _
  unfold packedEntryChunkBitOffset
  have hentryEnd := Nat.mul_le_mul_right width (show
      localWordIndex / packedChunkCount width wordSize + 1 <= entryCount by omega)
  have hexpand :
      (localWordIndex / packedChunkCount width wordSize + 1) * width =
        localWordIndex / packedChunkCount width wordSize * width + width := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- The classifier's range is inside the exact canonical component payload. -/
theorem packedReviewerInteriorLocation_fitsComponent
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    (packedReviewerInteriorLocation shape.size component localWordIndex).bitOffset +
        (packedReviewerInteriorLocation shape.size component localWordIndex).readWidth <=
      (packedReviewerInteriorCanonicalPayload shape component).length := by
  have hword : 0 < packedBpCodeWordWidth shape.size := by
    unfold packedBpCodeWordWidth
    exact SuccinctRank.machineWordBits_pos _
  have hwidth := packedReviewerInteriorEntryWidth_pos shape component
  have hlocal' :
      localWordIndex <
        packedReviewerInteriorEntryCount shape.size component *
          packedChunkCount (packedReviewerInteriorEntryWidth shape.size component)
            (packedBpCodeWordWidth shape.size) := by
    rw [packedReviewerInteriorCanonicalWords_length shape component,
      packedReviewerInteriorComponentWordCount,
      packedReviewerInteriorTableWords_eq_chunkCount
        (packedReviewerInteriorEntryCount shape.size component)
        (packedReviewerInteriorEntryWidth shape.size component)
        (packedBpCodeWordWidth shape.size) hword] at hlocal
    exact hlocal
  have hfit := packedReviewerInteriorEntryChunk_fits hwidth hword hlocal'
  rw [packedReviewerInteriorCanonicalPayload_length shape component]
  simpa [packedReviewerInteriorLocation] using hfit

/-- Every actual short component word fits one reviewer-memory cell in width. -/
theorem packedReviewerInteriorReadWidth_le_cellWidth
    (n : Nat) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat) :
    (packedReviewerInteriorLocation n component localWordIndex).readWidth <=
      packedReviewerCellWidth n := by
  have hchunk :
      (packedReviewerInteriorLocation n component localWordIndex).readWidth <=
        packedBpCodeWordWidth n := by
    unfold packedReviewerInteriorLocation packedEntryChunkReadWidth
    exact Nat.min_le_right _ _
  have hword : packedBpCodeWordWidth n <= packedReviewerCellWidth n := by
    unfold packedBpCodeWordWidth
    apply packedReviewerMachineWordBits_le_cellWidth
    have htwo := packedTwoMul_le_reviewerBound n
    omega
  exact Nat.le_trans hchunk hword

/-- The component append preserves the tagged word and its multiplicity. -/
theorem packedReviewerInteriorStoreAccess
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    (packedInteriorStoreWords shape)[
        packedReviewerInteriorComponentWordPrefix shape.size component +
          localWordIndex]? =
      (packedReviewerInteriorCanonicalWords shape component)[localWordIndex]? := by
  have hprefix := packedReviewerInteriorComponentWordPrefix_eq shape component
  cases component
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorBaselineAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorMinRelAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorMaxRelAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorArgOffsetAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorLocalAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorGlobalAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorLocalLevelAccess shape hlocal
  · rw [hprefix]
    simpa [packedReviewerInteriorCanonicalWords] using
      packedInteriorGlobalLevelAccess shape localWordIndex

/-! ## Physical request/reply surface -/

/-- Size/header/reply-derived offset of the interior directory in the payload. -/
def packedReviewerInteriorPayloadOffset
    (n longCount sparseCount : Nat) : Nat :=
  2 * n + packedReviewerAccessLength n longCount sparseCount

/-- Absolute padded-bit address of a classified interior word. -/
def packedReviewerInteriorBitAddress
    (n longCount sparseCount : Nat) (location : PackedReviewerInteriorLocation) :
    Nat :=
  packedReviewerCellWidth n +
    packedReviewerInteriorPayloadOffset n longCount sparseCount +
      location.componentBitPrefix + location.bitOffset

/-- The one-or-two-cell physical request plan for one classified word. -/
def packedReviewerInteriorLocationPlan
    (n longCount sparseCount : Nat) (location : PackedReviewerInteriorLocation) :
    List Nat :=
  packedReviewerProbePlan n
    (packedReviewerInteriorBitAddress n longCount sparseCount location)
    location.readWidth

/-- The plan for a segment-local word; out-of-range words issue no request. -/
def packedReviewerInteriorReadPlan
    (n longCount sparseCount index : Nat) : List Nat :=
  match packedReviewerInteriorClassify n index with
  | none => []
  | some location =>
      packedReviewerInteriorLocationPlan n longCount sparseCount location

/--
Read one canonical segment-20 word solely from replies supplied by the given
physical reviewer memory.  The memory is external to the classifier.
-/
def packedReviewerInteriorRead
    (n longCount sparseCount : Nat) (memory : List (List Bool))
    (index : Nat) : Option (List Bool) :=
  match packedReviewerInteriorClassify n index with
  | none => none
  | some location =>
      (packedFetch memory
        (packedReviewerInteriorLocationPlan n longCount sparseCount location)).map
          (packedReviewerDecodeSpan n
            (packedReviewerInteriorBitAddress n longCount sparseCount location)
            location.readWidth)

/-- Each logical segment-20 word issues at most two physical cell requests. -/
theorem packedReviewerInteriorReadPlan_length_le_two
    (n longCount sparseCount index : Nat) :
    (packedReviewerInteriorReadPlan n longCount sparseCount index).length <= 2 := by
  unfold packedReviewerInteriorReadPlan packedReviewerInteriorLocationPlan
  split
  · simp
  · exact packedReviewerProbeCount_le_two _ _ _

/-- The read is definitionally absent when the classifier is absent. -/
theorem packedReviewerInteriorRead_eq_none_of_classify_none
    {n longCount sparseCount index : Nat} {memory : List (List Bool)}
    (hclassify : packedReviewerInteriorClassify n index = none) :
    packedReviewerInteriorRead n longCount sparseCount memory index = none := by
  simp [packedReviewerInteriorRead, hclassify]

/-! ## The actual reviewer-memory lowering -/

/-- The closed interior offset is the canonical shape-facing close offset. -/
theorem packedReviewerInteriorPayloadOffset_eq (shape : CartesianShape) :
    packedReviewerInteriorPayloadOffset shape.size (longCount shape)
        (packedReviewerSparseCount shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset shape := by
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have haccess := packedReviewerAccessLength_eq shape
  unfold packedReviewerInteriorPayloadOffset
    concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
  dsimp only
  omega

/-- A payload range, shifted past the header cell, is the same padded-bit range. -/
theorem packedReviewerInteriorPayloadSlice
    (shape : CartesianShape) (j width : Nat)
    (hfit : j + width <=
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape)) :
    ((packedReviewerPaddedBits shape).drop
        (packedReviewerCellWidth shape.size + j)).take width =
      ((packedReviewerPayloadBits shape).drop j).take width := by
  have hhdr := packedReviewerHeaderBits_length shape
  have hpay := packedReviewerPayloadBits_length_eq shape
  have hjle : j <= (packedReviewerPayloadBits shape).length := by omega
  have hwle : width <= ((packedReviewerPayloadBits shape).drop j).length := by
    rw [List.length_drop]
    omega
  unfold packedReviewerPaddedBits packedReviewerSerializedBits
  rw [List.append_assoc, ← List.drop_drop]
  rw [← hhdr, List.drop_left]
  rw [List.drop_append_of_le_length hjle, List.take_append_of_le_length hwle]

/-- A component-local classified range lies in the full interior directory. -/
theorem packedReviewerInteriorLocation_fitsDirectory
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    packedReviewerInteriorComponentBitPrefix shape.size component +
          (packedReviewerInteriorLocation shape.size component
            localWordIndex).bitOffset +
        (packedReviewerInteriorLocation shape.size component
          localWordIndex).readWidth <=
      (canonicalRelativeRmmInteriorDirectory shape).payload.length := by
  have hcomponent :=
    packedReviewerInteriorLocation_fitsComponent shape component localWordIndex hlocal
  obtain ⟨suffix, hdecompose⟩ :=
    packedReviewerInteriorDirectory_decompose shape component
  have hprefix := packedReviewerInteriorComponentBitPrefix_eq shape component
  rw [hdecompose, List.length_append, List.length_append]
  omega

/-- The same range lies in the exact consumed payload. -/
theorem packedReviewerInteriorLocation_fitsPayload
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    packedReviewerInteriorPayloadOffset shape.size (longCount shape)
          (packedReviewerSparseCount shape) +
        packedReviewerInteriorComponentBitPrefix shape.size component +
          (packedReviewerInteriorLocation shape.size component
            localWordIndex).bitOffset +
        (packedReviewerInteriorLocation shape.size component
          localWordIndex).readWidth <=
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  have hdir :=
    packedReviewerInteriorLocation_fitsDirectory shape component localWordIndex hlocal
  have hinterior :=
    canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw shape
  unfold packedReviewerInteriorPayloadOffset packedReviewerPayloadLength
  omega

/-- The absolute request range is inside the allocated reviewer memory. -/
theorem packedReviewerInteriorLocation_fitsAllocation
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    packedReviewerInteriorBitAddress shape.size (longCount shape)
          (packedReviewerSparseCount shape)
          (packedReviewerInteriorLocation shape.size component localWordIndex) +
        (packedReviewerInteriorLocation shape.size component
          localWordIndex).readWidth <=
      packedReviewerAllocatedBits shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  have hpayload :=
    packedReviewerInteriorLocation_fitsPayload shape component localWordIndex hlocal
  have hserialized := packedReviewerSerialized_le_allocated shape.size
    (longCount shape) (packedReviewerSparseCount shape)
  unfold packedReviewerInteriorBitAddress
  change packedReviewerCellWidth shape.size +
          packedReviewerInteriorPayloadOffset shape.size (longCount shape)
              (packedReviewerSparseCount shape) +
            packedReviewerInteriorComponentBitPrefix shape.size component +
          (packedReviewerInteriorLocation shape.size component
              localWordIndex).bitOffset +
        (packedReviewerInteriorLocation shape.size component
          localWordIndex).readWidth <=
      packedReviewerAllocatedBits shape.size (longCount shape)
        (packedReviewerSparseCount shape)
  omega

/-!
The physical decoding theorem expands a large canonical payload expression.
The local heartbeat allowance is compilation fuel only; it is not executable
state and does not weaken the theorem.
-/

set_option maxHeartbeats 800000 in
/--
The padded reviewer-memory bit range for one concrete component location is the
exact entry-local payload chunk.
-/
theorem packedReviewerInteriorPhysicalSlice
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    let location :=
      packedReviewerInteriorLocation shape.size component localWordIndex
    ((packedReviewerPaddedBits shape).drop
        (packedReviewerInteriorBitAddress shape.size (longCount shape)
          (packedReviewerSparseCount shape) location)).take location.readWidth =
      ((packedReviewerInteriorCanonicalPayload shape component).drop
        location.bitOffset).take location.readWidth := by
  dsimp only
  let location :=
    packedReviewerInteriorLocation shape.size component localWordIndex
  have hcomponent := packedReviewerInteriorLocation_fitsComponent shape
    component localWordIndex hlocal
  have hdirectory := packedReviewerInteriorLocation_fitsDirectory shape
    component localWordIndex hlocal
  have hpayload := packedReviewerInteriorLocation_fitsPayload shape
    component localWordIndex hlocal
  have hpadded := packedReviewerInteriorPayloadSlice shape
    (packedReviewerInteriorPayloadOffset shape.size (longCount shape)
        (packedReviewerSparseCount shape) +
      packedReviewerInteriorComponentBitPrefix shape.size component +
        location.bitOffset)
    location.readWidth hpayload
  have hinterior := packedReviewerPayload_interiorSlice shape
    (off := packedReviewerInteriorComponentBitPrefix shape.size component +
      location.bitOffset)
    (len := location.readWidth) hdirectory
  have hcomponentSlice := packedReviewerInteriorDirectorySlice shape
    component (off := location.bitOffset) (len := location.readWidth)
    hcomponent
  have hpadded' :
      ((packedReviewerPaddedBits shape).drop
          (packedReviewerInteriorBitAddress shape.size (longCount shape)
            (packedReviewerSparseCount shape) location)).take location.readWidth =
        ((packedReviewerPayloadBits shape).drop
          (packedReviewerInteriorPayloadOffset shape.size (longCount shape)
              (packedReviewerSparseCount shape) +
            packedReviewerInteriorComponentBitPrefix shape.size component +
              location.bitOffset)).take
          location.readWidth := by
    rw [show
        packedReviewerInteriorBitAddress shape.size (longCount shape)
            (packedReviewerSparseCount shape) location =
          packedReviewerCellWidth shape.size +
            (packedReviewerInteriorPayloadOffset shape.size (longCount shape)
                (packedReviewerSparseCount shape) +
              packedReviewerInteriorComponentBitPrefix shape.size component +
                location.bitOffset) by
      unfold packedReviewerInteriorBitAddress
      dsimp only [location, packedReviewerInteriorLocation]
      omega]
    exact hpadded
  have hinterior' :
      ((packedReviewerPayloadBits shape).drop
          (packedReviewerInteriorPayloadOffset shape.size (longCount shape)
              (packedReviewerSparseCount shape) +
            packedReviewerInteriorComponentBitPrefix shape.size component +
              location.bitOffset)).take
          location.readWidth =
        ((canonicalRelativeRmmInteriorDirectory shape).payload.drop
          (packedReviewerInteriorComponentBitPrefix shape.size component +
            location.bitOffset)).take
          location.readWidth := by
    rw [packedReviewerInteriorPayloadOffset_eq shape]
    rw [show
        concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset shape +
              packedReviewerInteriorComponentBitPrefix shape.size component +
                location.bitOffset =
            concreteBPNativeSuccinctRMQCanonicalReviewerCloseBitOffset shape +
              (packedReviewerInteriorComponentBitPrefix shape.size component +
                location.bitOffset) by omega]
    exact hinterior
  rw [hpadded', hinterior', hcomponentSlice]

set_option maxHeartbeats 800000 in
/--
Fetching the exact cells for one concrete component location from reviewer
memory decodes to that component's exact entry-local chunk.
-/
theorem packedReviewerInteriorLocationDecode
    (shape : CartesianShape) (component : PackedReviewerInteriorComponentTag)
    (localWordIndex : Nat)
    (hlocal : localWordIndex <
      (packedReviewerInteriorCanonicalWords shape component).length) :
    let location :=
      packedReviewerInteriorLocation shape.size component localWordIndex
    (packedFetch (packedReviewerMemory shape)
        (packedReviewerInteriorLocationPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) location)).map
      (packedReviewerDecodeSpan shape.size
        (packedReviewerInteriorBitAddress shape.size (longCount shape)
          (packedReviewerSparseCount shape) location) location.readWidth) =
      some (((packedReviewerInteriorCanonicalPayload shape component).drop
        location.bitOffset).take location.readWidth) := by
  dsimp only
  let location :=
    packedReviewerInteriorLocation shape.size component localWordIndex
  have hallocation := packedReviewerInteriorLocation_fitsAllocation shape
    component localWordIndex hlocal
  have hwidth := packedReviewerInteriorReadWidth_le_cellWidth shape.size
    component localWordIndex
  have hdecode := packedReviewerProbePlan_decode shape hwidth hallocation
  have hslice := packedReviewerInteriorPhysicalSlice shape component
    localWordIndex hlocal
  unfold packedReviewerInteriorLocationPlan
  rw [hdecode]
  congr 1

/--
For a successful classification, fetching the classified physical cells from the
actual reviewer memory decodes to the exact component-local chunk.
-/
theorem packedReviewerInteriorRead_of_classify
    (shape : CartesianShape) {index : Nat}
    {location : PackedReviewerInteriorLocation}
    (hclassify : packedReviewerInteriorClassify shape.size index = some location) :
    packedReviewerInteriorRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) index =
      some (((packedReviewerInteriorCanonicalPayload shape location.component).drop
          location.bitOffset).take location.readWidth) := by
  obtain ⟨hlocation, _hindex, hlocal⟩ :=
    packedReviewerInteriorClassify_sound hclassify
  have hlocal' :
      location.localWordIndex <
        (packedReviewerInteriorCanonicalWords shape location.component).length := by
    rw [packedReviewerInteriorCanonicalWords_length shape location.component]
    exact hlocal
  unfold packedReviewerInteriorRead
  simp only [hclassify]
  rw [hlocation]
  exact packedReviewerInteriorLocationDecode shape location.component
    location.localWordIndex hlocal'

/-- The canonical segment-20 word list has the closed total word count. -/
theorem packedReviewerInteriorStoreWords_length (shape : CartesianShape) :
    (packedInteriorStoreWords shape).length =
      packedInteriorComponentWords shape.size := by
  unfold packedInteriorStoreWords
  simpa using packedInteriorComponentWords_eq shape

/--
**Aggregate segment-20 physical lowering.** For every word index—including an
index outside the ragged store—the reviewer-memory read option is exactly the
canonical logical segment-20 read option.
-/
theorem packedReviewerInteriorRead_eq_segment20
    (shape : CartesianShape) (index : Nat) :
    packedReviewerInteriorRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) index =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 index := by
  cases hclassify : packedReviewerInteriorClassify shape.size index with
  | none =>
      have hge :=
        (packedReviewerInteriorClassify_eq_none_iff shape.size index).1 hclassify
      have hnoneList : (packedInteriorStoreWords shape)[index]? = none := by
        apply List.getElem?_eq_none
        rw [packedReviewerInteriorStoreWords_length shape]
        exact hge
      have hnoneArray :
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[index]? =
            none := by
        calc
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[index]? =
              (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList[index]? := by
                rw [Array.getElem?_toList]
          _ = none := hnoneList
      rw [packedReviewerInteriorRead_eq_none_of_classify_none hclassify,
        packedExecutedStore_interiorComponentSegment shape index, hnoneArray]
  | some location =>
      obtain ⟨hlocation, hindex, hlocal⟩ :=
        packedReviewerInteriorClassify_sound hclassify
      have hlocal' :
          location.localWordIndex <
            (packedReviewerInteriorCanonicalWords shape
              location.component).length := by
        rw [packedReviewerInteriorCanonicalWords_length shape location.component]
        exact hlocal
      have hstore := packedReviewerInteriorStoreAccess shape location.component
        location.localWordIndex hlocal'
      have hword := packedReviewerInteriorCanonicalWord shape location.component
        location.localWordIndex hlocal'
      have hword' :
          (packedReviewerInteriorCanonicalWords shape
              location.component)[location.localWordIndex]? =
            some (((packedReviewerInteriorCanonicalPayload shape
                location.component).drop location.bitOffset).take
              location.readWidth) := by
        rw [hlocation]
        exact hword
      have hlist :
          (packedInteriorStoreWords shape)[index]? =
            (packedReviewerInteriorCanonicalWords shape
              location.component)[location.localWordIndex]? := by
        rw [hindex]
        exact hstore
      have harray :
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[index]? =
            (packedReviewerInteriorCanonicalWords shape
              location.component)[location.localWordIndex]? := by
        calc
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[index]? =
              (canonicalRelativeRmmInteriorComponentStore shape).store.words.toList[index]? := by
                rw [Array.getElem?_toList]
          _ = (packedReviewerInteriorCanonicalWords shape
              location.component)[location.localWordIndex]? := hlist
      rw [packedReviewerInteriorRead_of_classify shape hclassify,
        packedExecutedStore_interiorComponentSegment shape index, harray, hword']

/-- The same aggregate equality in the logical-to-physical orientation. -/
theorem packedReviewerSegment20_eq_interiorRead
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 index =
      packedReviewerInteriorRead shape.size (longCount shape)
        (packedReviewerSparseCount shape) (packedReviewerMemory shape) index :=
  (packedReviewerInteriorRead_eq_segment20 shape index).symm

end PackedCellProbe
end SuccinctFinal
end RMQ

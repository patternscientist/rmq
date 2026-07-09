import RMQ.Core.SuccinctFinal.RAM.Segments

/-!
# Flat-payload backing for the final BP-native succinct RMQ RAM bridge

This module contains the query-independent flat payload layout, source/backing
manifest, flat read store, and successful-read backing predicates used by the
compatibility root `RMQ.Core.SuccinctFinalRAM`.
-/

namespace RMQ
namespace SuccinctFinal

/-! ### Flat payload backing for the globally segmented final store -/

/--
Counted component slices of the final flat RMQ payload.

The access padding and close padding are represented in the layout below, but
no final global read segment is backed by padding.
-/
inductive ConcreteBPNativeSuccinctRMQFlatPayloadComponent where
  | bpCode
  | accessRankPayload
  | selectPayload
  | closePayload
deriving DecidableEq

/--
Concrete word source for one final global read segment.

The source names are deliberately more precise than the four counted payload
components: they record the table or alias a segment reads, while the backing
record below maps that source into the flat counted component.
-/
inductive ConcreteBPNativeSuccinctRMQFlatPayloadSource where
  | bpCode
  | selectSuperBaseOccurrence
  | selectSuperBaseWordIndex
  | selectSuperRankBefore
  | selectSuperFirstOffset
  | selectLocalBaseOccurrence
  | selectLocalBaseWordIndex
  | selectLocalRankBefore
  | selectLocalFirstOffset
  | selectLongFlagRankSuperTrue
  | selectLongFlagRankBlockTrue
  | selectLongFlagBits
  | selectLongRelative
  | selectSparseRankSuperTrue
  | selectSparseRankBlockTrue
  | selectSparseFlagBits
  | selectSparseRelative
  | finalRankSuperFalse
  | finalRankBlockFalse
  | finalRankBPCodeAlias
  | closeSummaryBaseline
  | closeSummaryMinRel
  | closeSummaryMaxRel
  | closeSummaryArgOffset
  | closeInteriorLocal
  | closeInteriorGlobal
  | closeFiniteSmallInteriorMin
  | closeFiniteSmallInteriorArg
  | closeFiniteSmallSameBlock
deriving DecidableEq

structure ConcreteBPNativeSuccinctRMQFlatPayloadLayout
    (shape : Cartesian.CartesianShape) where
  payload : List Bool
  bpCodePayload : List Bool
  accessRankPayload : List Bool
  selectPayload : List Bool
  accessPadding : List Bool
  closePayload : List Bool
  closePadding : List Bool

def concreteBPNativeSuccinctRMQFlatPayloadLayout
    (shape : Cartesian.CartesianShape) :
    ConcreteBPNativeSuccinctRMQFlatPayloadLayout shape :=
  let accessDirectory :=
    builtGenericSparseExceptionSelectBPCloseAccessDirectory shape
  let rankData := builtRelativeSplitBPCloseRankData shape
  let selectSource :=
    GenericSelect.sparseExceptionSelectSource shape.bpCode false
  let closeDirectory := concreteBPNativeCloseDirectory shape
  let accessPadding :=
    List.replicate
      (genericSparseExceptionBPCloseAccessOverhead shape.size -
        accessDirectory.payload.length) false
  let closePadding :=
    List.replicate
      (SuccinctClose.compactBPCloseOverhead shape.size -
        closeDirectory.payload.length) false
  { payload :=
      concreteBPNativeSuccinctRMQPayload
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape
    bpCodePayload := shape.bpCode
    accessRankPayload := rankData.auxPayload
    selectPayload := selectSource.payload
    accessPadding := accessPadding
    closePayload := closeDirectory.payload
    closePadding := closePadding }

def ConcreteBPNativeSuccinctRMQFlatPayloadLayout.componentPayload
    {shape : Cartesian.CartesianShape}
    (layout : ConcreteBPNativeSuccinctRMQFlatPayloadLayout shape) :
    ConcreteBPNativeSuccinctRMQFlatPayloadComponent -> List Bool
  | .bpCode => layout.bpCodePayload
  | .accessRankPayload => layout.accessRankPayload
  | .selectPayload => layout.selectPayload
  | .closePayload => layout.closePayload

def concreteBPNativeSuccinctRMQFlatPayloadComponentPayload
    (shape : Cartesian.CartesianShape) :
    ConcreteBPNativeSuccinctRMQFlatPayloadComponent -> List Bool
  | .bpCode => shape.bpCode
  | .accessRankPayload =>
      (builtRelativeSplitBPCloseRankData shape).auxPayload
  | .selectPayload =>
      (GenericSelect.sparseExceptionSelectSource shape.bpCode false).payload
  | .closePayload =>
      (concreteBPNativeCloseDirectory shape).payload

@[simp] theorem concreteBPNativeSuccinctRMQFlatPayloadLayout_componentPayload_eq
    (shape : Cartesian.CartesianShape)
    (component : ConcreteBPNativeSuccinctRMQFlatPayloadComponent) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentPayload
        component =
      concreteBPNativeSuccinctRMQFlatPayloadComponentPayload
        shape component := by
  cases component <;> rfl

def ConcreteBPNativeSuccinctRMQFlatPayloadLayout.componentFlatOffset
    {shape : Cartesian.CartesianShape}
    (layout : ConcreteBPNativeSuccinctRMQFlatPayloadLayout shape) :
    ConcreteBPNativeSuccinctRMQFlatPayloadComponent -> Nat
  | .bpCode => 0
  | .accessRankPayload => layout.bpCodePayload.length
  | .selectPayload =>
      layout.bpCodePayload.length + layout.accessRankPayload.length
  | .closePayload =>
      layout.bpCodePayload.length + layout.accessRankPayload.length +
        layout.selectPayload.length + layout.accessPadding.length

theorem concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_eq
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload =
      concreteBPNativeSuccinctRMQPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape := by
  rfl

theorem concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_length
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload.length =
      2 * n +
        concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead n := by
  rw [concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_eq]
  exact
    concreteBPNativeSuccinctRMQPayload_length
      builtGenericSparseExceptionSelectBPCloseAccessFamily hshape

theorem concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_components
    (shape : Cartesian.CartesianShape) :
    let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
    layout.payload =
      layout.bpCodePayload ++ layout.accessRankPayload ++
        layout.selectPayload ++ layout.accessPadding ++
          layout.closePayload ++ layout.closePadding := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadLayout,
    concreteBPNativeSuccinctRMQPayload,
    concreteBPNativeSuccinctRMQAuxPayload,
    builtGenericSparseExceptionSelectBPCloseAccessFamily,
    builtGenericSparseExceptionSelectBPCloseAccessDirectory,
    List.append_assoc]

@[simp] private theorem list_drop_append_length
    {α : Type} (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  simp

@[simp] private theorem list_take_append_length
    {α : Type} (xs ys : List α) :
    (xs ++ ys).take xs.length = xs := by
  simp

@[simp] private theorem list_drop_append_length_add
    {α : Type} (xs ys : List α) (n : Nat) :
    (xs ++ ys).drop (xs.length + n) = ys.drop n := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [Nat.succ_add, ih]

@[simp] private theorem list_drop_prefix_take_self
    {α : Type} (pref middle suffix : List α) :
    ((pref ++ middle ++ suffix).drop pref.length).take
        middle.length = middle := by
  simp [List.append_assoc]

private theorem list_slice_trans
    {α : Type} (payload component source : List α)
    (base offset : Nat)
    (hcomponent :
      (payload.drop base).take component.length = component)
    (hsource :
      (component.drop offset).take source.length = source) :
    (payload.drop (base + offset)).take source.length = source := by
  by_cases hzero : source.length = 0
  · have hnil : source = [] := List.length_eq_zero_iff.mp hzero
    simp [hnil]
  · have hlen := congrArg List.length hsource
    simp [List.length_take, List.length_drop] at hlen
    have hle : source.length <= component.length - offset := by
      omega
    have htake :
        (((payload.drop base).take component.length).drop offset).take
            source.length =
          ((payload.drop base).drop offset).take source.length := by
      rw [List.drop_take, List.take_take]
      simp [Nat.min_eq_left hle]
    calc
      (payload.drop (base + offset)).take source.length =
          ((payload.drop base).drop offset).take source.length := by
            rw [← List.drop_drop]
      _ =
          (((payload.drop base).take component.length).drop offset).take
              source.length := htake.symm
      _ = (component.drop offset).take source.length := by
            rw [hcomponent]
      _ = source := hsource

theorem concreteBPNativeSuccinctRMQFlatPayloadLayout_component_slice
    (shape : Cartesian.CartesianShape)
    (component : ConcreteBPNativeSuccinctRMQFlatPayloadComponent) :
    let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
    (layout.payload.drop (layout.componentFlatOffset component)).take
        (layout.componentPayload component).length =
      layout.componentPayload component := by
  intro layout
  have hcomponents :=
    concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_components shape
  change
      (layout.payload.drop (layout.componentFlatOffset component)).take
          (layout.componentPayload component).length =
        layout.componentPayload component
  cases component <;>
    simp [layout,
      ConcreteBPNativeSuccinctRMQFlatPayloadLayout.componentPayload,
      ConcreteBPNativeSuccinctRMQFlatPayloadLayout.componentFlatOffset,
      hcomponents, List.append_assoc, Nat.add_assoc]

def concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? :
    Nat -> Option ConcreteBPNativeSuccinctRMQFlatPayloadSource
  | 0 => some .bpCode
  | 1 => some .selectSuperBaseOccurrence
  | 2 => some .selectSuperBaseWordIndex
  | 3 => some .selectSuperRankBefore
  | 4 => some .selectSuperFirstOffset
  | 5 => some .selectLocalBaseOccurrence
  | 6 => some .selectLocalBaseWordIndex
  | 7 => some .selectLocalRankBefore
  | 8 => some .selectLocalFirstOffset
  | 9 => some .selectLongFlagRankSuperTrue
  | 10 => some .selectLongFlagRankBlockTrue
  | 11 => some .selectLongFlagBits
  | 12 => some .selectLongRelative
  | 13 => some .selectSparseRankSuperTrue
  | 14 => some .selectSparseRankBlockTrue
  | 15 => some .selectSparseFlagBits
  | 16 => some .selectSparseRelative
  | 17 => some .finalRankSuperFalse
  | 18 => some .finalRankBlockFalse
  | 19 => some .finalRankBPCodeAlias
  | 20 => some .closeSummaryBaseline
  | 21 => some .closeSummaryMinRel
  | 22 => some .closeSummaryMaxRel
  | 23 => some .closeSummaryArgOffset
  | 24 => some .closeInteriorLocal
  | 25 => some .closeInteriorGlobal
  -- Legacy dead interior slots. They keep manifest names for compatibility,
  -- but their source word/payload views are empty and they are never counted.
  | 26 => some .closeFiniteSmallInteriorMin
  | 27 => some .closeFiniteSmallInteriorArg
  | 28 => some .closeFiniteSmallSameBlock
  | _ + 29 => none

def concreteBPNativeSuccinctRMQFlatPayloadSourceComponent :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource ->
      ConcreteBPNativeSuccinctRMQFlatPayloadComponent
  | .bpCode => .bpCode
  | .selectSuperBaseOccurrence => .selectPayload
  | .selectSuperBaseWordIndex => .selectPayload
  | .selectSuperRankBefore => .selectPayload
  | .selectSuperFirstOffset => .selectPayload
  | .selectLocalBaseOccurrence => .selectPayload
  | .selectLocalBaseWordIndex => .selectPayload
  | .selectLocalRankBefore => .selectPayload
  | .selectLocalFirstOffset => .selectPayload
  | .selectLongFlagRankSuperTrue => .selectPayload
  | .selectLongFlagRankBlockTrue => .selectPayload
  | .selectLongFlagBits => .selectPayload
  | .selectLongRelative => .selectPayload
  | .selectSparseRankSuperTrue => .selectPayload
  | .selectSparseRankBlockTrue => .selectPayload
  | .selectSparseFlagBits => .selectPayload
  | .selectSparseRelative => .selectPayload
  | .finalRankSuperFalse => .accessRankPayload
  | .finalRankBlockFalse => .accessRankPayload
  | .finalRankBPCodeAlias => .bpCode
  | .closeSummaryBaseline => .closePayload
  | .closeSummaryMinRel => .closePayload
  | .closeSummaryMaxRel => .closePayload
  | .closeSummaryArgOffset => .closePayload
  | .closeInteriorLocal => .closePayload
  | .closeInteriorGlobal => .closePayload
  | .closeFiniteSmallInteriorMin => .closePayload
  | .closeFiniteSmallInteriorArg => .closePayload
  | .closeFiniteSmallSameBlock => .closePayload

def concreteBPNativeSuccinctRMQFlatPayloadSourceAliasesCountedPayload :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Bool
  | .finalRankBPCodeAlias => true
  | _ => false

def concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat
    (shape : Cartesian.CartesianShape) :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Prop
  | .closeSummaryBaseline =>
      SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
  | .closeSummaryMinRel =>
      SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
  | .closeSummaryMaxRel =>
      SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
  | .closeSummaryArgOffset =>
      SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
  | .closeInteriorLocal =>
      SuccinctClose.concreteBPRelativeRmmInteriorReady shape
  | .closeInteriorGlobal =>
      SuccinctClose.concreteBPRelativeRmmInteriorReady shape
  | .closeFiniteSmallInteriorMin =>
      False
  | .closeFiniteSmallInteriorArg =>
      False
  | .closeFiniteSmallSameBlock =>
      False
  | _ => True

def concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
    (shape : Cartesian.CartesianShape) (segment : Nat) : Prop :=
  match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
  | some source =>
      concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat shape source
  | none => False

def concreteBPNativeSuccinctRMQFlatPayloadSourceLargeReadyCounted :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Prop
  | .closeFiniteSmallInteriorMin => False
  | .closeFiniteSmallInteriorArg => False
  | .closeFiniteSmallSameBlock => False
  | _ => True

theorem concreteBPNativeSuccinctRMQFlatPayloadFiniteSmallSegmentStatus
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? 26 =
        some .closeFiniteSmallInteriorMin /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? 27 =
        some .closeFiniteSmallInteriorArg /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? 28 =
        some .closeFiniteSmallSameBlock /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape 26 /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape 27 /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape 28 /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSourceLargeReadyCounted
        .closeFiniteSmallInteriorMin /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSourceLargeReadyCounted
        .closeFiniteSmallInteriorArg /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSourceLargeReadyCounted
        .closeFiniteSmallSameBlock := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
    concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat,
    concreteBPNativeSuccinctRMQFlatPayloadSourceLargeReadyCounted]

/--
Compatibility status for the retired all-pairs interior slots.

Segments `26` and `27` still have manifest names, but they are legacy
compatibility slots in the public flat payload: they are not counted and their
source word/payload views are empty.
-/
theorem concreteBPNativeSuccinctRMQFlatPayloadLegacyInteriorSegmentStatus
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? 26 =
        some .closeFiniteSmallInteriorMin /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? 27 =
        some .closeFiniteSmallInteriorArg /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape 26 /\
      ¬ concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          shape 27 := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
    concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]

def concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
    (shape : Cartesian.CartesianShape) :
    ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  let selectData := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let rankData := builtRelativeSplitBPCloseRankData shape
  let summary :=
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
  fun
  | .bpCode => 0
  | .selectSuperBaseOccurrence => 0
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseOccurrenceTable.payload.length
  | .selectSuperRankBefore =>
      selectData.superTable.baseOccurrenceTable.payload.length +
        selectData.superTable.baseWordIndexTable.payload.length
  | .selectSuperFirstOffset =>
      selectData.superTable.baseOccurrenceTable.payload.length +
        selectData.superTable.baseWordIndexTable.payload.length +
          selectData.superTable.rankBeforeTable.payload.length
  | .selectLongFlagBits =>
      selectData.superTable.payload.length
  | .selectLongFlagRankSuperTrue =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length
  | .selectLongFlagRankBlockTrue =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.superTables.payload.length
  | .selectLongRelative =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length
  | .selectLocalBaseOccurrence =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length
  | .selectLocalBaseWordIndex =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.baseOccurrenceTable.payload.length
  | .selectLocalRankBefore =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.baseOccurrenceTable.payload.length +
                selectData.localTable.baseWordIndexTable.payload.length
  | .selectLocalFirstOffset =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.baseOccurrenceTable.payload.length +
                selectData.localTable.baseWordIndexTable.payload.length +
                  selectData.localTable.rankBeforeTable.payload.length
  | .selectSparseFlagBits =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.payload.length
  | .selectSparseRankSuperTrue =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.payload.length +
                selectData.sparseDirectory.flagBits.length
  | .selectSparseRankBlockTrue =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.payload.length +
                selectData.sparseDirectory.flagBits.length +
                  selectData.sparseDirectory.rankData.superTables.payload.length
  | .selectSparseRelative =>
      selectData.superTable.payload.length +
        selectData.longFlagBits.length +
          selectData.longFlagRankData.auxPayload.length +
            selectData.longSuperRelativeTable.payload.length +
              selectData.localTable.payload.length +
                selectData.sparseDirectory.flagBits.length +
                  selectData.sparseDirectory.rankData.auxPayload.length
  | .finalRankSuperFalse =>
      rankData.superTables.trueTable.payload.length
  | .finalRankBlockFalse =>
      rankData.superTables.payload.length +
        rankData.blockTables.trueTable.payload.length
  | .finalRankBPCodeAlias => 0
  | .closeSummaryBaseline => 0
  | .closeSummaryMinRel =>
      summary.baselineTable.payload.length
  | .closeSummaryMaxRel =>
      summary.baselineTable.payload.length +
        summary.minRelTable.payload.length
  | .closeSummaryArgOffset =>
      summary.baselineTable.payload.length +
        summary.minRelTable.payload.length +
          summary.maxRelTable.payload.length
  | .closeInteriorLocal =>
      summary.payload.length
  | .closeInteriorGlobal =>
      summary.payload.length + localTable.payload.length
  | .closeFiniteSmallInteriorMin =>
      0
  | .closeFiniteSmallInteriorArg =>
      0
  | .closeFiniteSmallSameBlock => 0

def concreteBPNativeSuccinctRMQFlatPayloadSourceWords
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    Array (List Bool) :=
  let selectData := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let rankData := builtRelativeSplitBPCloseRankData shape
  let summary :=
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape
  match source with
  | .bpCode =>
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray
  | .selectSuperBaseOccurrence =>
      selectData.superTable.baseOccurrenceTable.store.words
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseWordIndexTable.store.words
  | .selectSuperRankBefore =>
      selectData.superTable.rankBeforeTable.store.words
  | .selectSuperFirstOffset =>
      selectData.superTable.firstOffsetTable.store.words
  | .selectLocalBaseOccurrence =>
      selectData.localTable.baseOccurrenceTable.store.words
  | .selectLocalBaseWordIndex =>
      selectData.localTable.baseWordIndexTable.store.words
  | .selectLocalRankBefore =>
      selectData.localTable.rankBeforeTable.store.words
  | .selectLocalFirstOffset =>
      selectData.localTable.firstOffsetTable.store.words
  | .selectLongFlagRankSuperTrue =>
      selectData.longFlagRankData.superTables.trueTable.store.words
  | .selectLongFlagRankBlockTrue =>
      selectData.longFlagRankData.blockTables.trueTable.store.words
  | .selectLongFlagBits =>
      selectData.longFlagRankData.bitWords.store.words
  | .selectLongRelative =>
      selectData.longSuperRelativeTable.store.words
  | .selectSparseRankSuperTrue =>
      selectData.sparseDirectory.rankData.superTables.trueTable.store.words
  | .selectSparseRankBlockTrue =>
      selectData.sparseDirectory.rankData.blockTables.trueTable.store.words
  | .selectSparseFlagBits =>
      selectData.sparseDirectory.rankData.bitWords.store.words
  | .selectSparseRelative =>
      selectData.sparseDirectory.relativeTable.store.words
  | .finalRankSuperFalse =>
      rankData.superTables.falseTable.store.words
  | .finalRankBlockFalse =>
      rankData.blockTables.falseTable.store.words
  | .finalRankBPCodeAlias =>
      rankData.bitWords.store.words
  | .closeSummaryBaseline =>
      summary.baselineTable.store.words
  | .closeSummaryMinRel =>
      summary.minRelTable.store.words
  | .closeSummaryMaxRel =>
      summary.maxRelTable.store.words
  | .closeSummaryArgOffset =>
      summary.argOffsetTable.store.words
  | .closeInteriorLocal =>
      localTable.table.store.words
  | .closeInteriorGlobal =>
      globalTable.table.store.words
  | .closeFiniteSmallInteriorMin =>
      #[]
  | .closeFiniteSmallInteriorArg =>
      #[]
  | .closeFiniteSmallSameBlock => #[]

def concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    List Bool :=
  let selectData := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let rankData := builtRelativeSplitBPCloseRankData shape
  let summary :=
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape
  match source with
  | .bpCode => shape.bpCode
  | .selectSuperBaseOccurrence =>
      selectData.superTable.baseOccurrenceTable.payload
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseWordIndexTable.payload
  | .selectSuperRankBefore =>
      selectData.superTable.rankBeforeTable.payload
  | .selectSuperFirstOffset =>
      selectData.superTable.firstOffsetTable.payload
  | .selectLocalBaseOccurrence =>
      selectData.localTable.baseOccurrenceTable.payload
  | .selectLocalBaseWordIndex =>
      selectData.localTable.baseWordIndexTable.payload
  | .selectLocalRankBefore =>
      selectData.localTable.rankBeforeTable.payload
  | .selectLocalFirstOffset =>
      selectData.localTable.firstOffsetTable.payload
  | .selectLongFlagRankSuperTrue =>
      selectData.longFlagRankData.superTables.trueTable.payload
  | .selectLongFlagRankBlockTrue =>
      selectData.longFlagRankData.blockTables.trueTable.payload
  | .selectLongFlagBits =>
      selectData.longFlagBits
  | .selectLongRelative =>
      selectData.longSuperRelativeTable.payload
  | .selectSparseRankSuperTrue =>
      selectData.sparseDirectory.rankData.superTables.trueTable.payload
  | .selectSparseRankBlockTrue =>
      selectData.sparseDirectory.rankData.blockTables.trueTable.payload
  | .selectSparseFlagBits =>
      selectData.sparseDirectory.flagBits
  | .selectSparseRelative =>
      selectData.sparseDirectory.relativeTable.payload
  | .finalRankSuperFalse =>
      rankData.superTables.falseTable.payload
  | .finalRankBlockFalse =>
      rankData.blockTables.falseTable.payload
  | .finalRankBPCodeAlias =>
      shape.bpCode
  | .closeSummaryBaseline =>
      summary.baselineTable.payload
  | .closeSummaryMinRel =>
      summary.minRelTable.payload
  | .closeSummaryMaxRel =>
      summary.maxRelTable.payload
  | .closeSummaryArgOffset =>
      summary.argOffsetTable.payload
  | .closeInteriorLocal =>
      localTable.payload
  | .closeInteriorGlobal =>
      globalTable.payload
  | .closeFiniteSmallInteriorMin =>
      []
  | .closeFiniteSmallInteriorArg =>
      []
  | .closeFiniteSmallSameBlock => []

theorem concreteBPNativeSuccinctRMQFlatPayloadLegacyInteriorSegment_empty
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords
        shape .closeFiniteSmallInteriorMin = #[] /\
      concreteBPNativeSuccinctRMQFlatPayloadSourceWords
        shape .closeFiniteSmallInteriorArg = #[] /\
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
        shape .closeFiniteSmallInteriorMin = [] /\
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
        shape .closeFiniteSmallInteriorArg = [] := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
    concreteBPNativeSuccinctRMQFlatPayloadSourcePayload]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem concreteBPNativeSuccinctRMQFlatPayloadSource_component_slice
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hcounted :
      concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat
        shape source) :
    let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
    ((layout.componentPayload
          (concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source)).drop
        (concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
          shape source)).take
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source).length =
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
        shape source := by
  have hdirect :
      ((concreteBPNativeSuccinctRMQFlatPayloadComponentPayload shape
            (concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source)).drop
          (concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
            shape source)).take
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
            shape source).length =
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source := by
    by_cases hready :
        SuccinctClose.concreteBPRelativeRmmInteriorReady shape
    · cases source <;>
        simp [concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat,
          concreteBPNativeSuccinctRMQFlatPayloadComponentPayload,
          concreteBPNativeSuccinctRMQFlatPayloadSourceComponent,
          concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset,
          concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
          GenericSelect.sparseExceptionSelectSource,
          GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource,
          GenericSelect.SparseExceptionSelectData.payload,
          GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.payload,
          GenericSelect.SparseExceptionDirectory.payload,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.auxPayload,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superPayload,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockPayload,
          SuccinctSpace.FixedWidthRankSampleTables.payload,
          concreteBPNativeCloseDirectory,
          SuccinctClose.concreteCompactBPCloseLCADirectory,
          SuccinctClose.concreteBPRelativeRmmInteriorDirectory,
          SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
          SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload,
          SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload,
          hready, List.append_assoc, Nat.add_assoc] at hcounted ⊢
    · by_cases hactive :
          SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · cases source <;>
          simp [concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat,
            concreteBPNativeSuccinctRMQFlatPayloadComponentPayload,
            concreteBPNativeSuccinctRMQFlatPayloadSourceComponent,
            concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset,
            concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
            GenericSelect.sparseExceptionSelectSource,
            GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource,
            GenericSelect.SparseExceptionSelectData.payload,
            GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.payload,
            GenericSelect.SparseExceptionDirectory.payload,
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.auxPayload,
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superPayload,
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockPayload,
            SuccinctSpace.FixedWidthRankSampleTables.payload,
            concreteBPNativeCloseDirectory,
            SuccinctClose.concreteCompactBPCloseLCADirectory,
            SuccinctClose.concreteBPRelativeRmmInteriorDirectory,
            SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
            SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload,
            hready, hactive, List.append_assoc, Nat.add_assoc] at hcounted ⊢
      · cases source <;>
          simp [concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat,
            concreteBPNativeSuccinctRMQFlatPayloadComponentPayload,
            concreteBPNativeSuccinctRMQFlatPayloadSourceComponent,
            concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset,
            concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
            GenericSelect.sparseExceptionSelectSource,
            GenericSelect.SparseExceptionSelectData.toChargedSelectPositionSource,
            GenericSelect.SparseExceptionSelectData.payload,
            GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.payload,
            GenericSelect.SparseExceptionDirectory.payload,
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.auxPayload,
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superPayload,
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockPayload,
            SuccinctSpace.FixedWidthRankSampleTables.payload,
            concreteBPNativeCloseDirectory,
            SuccinctClose.concreteCompactBPCloseLCADirectory,
            SuccinctClose.concreteBPRelativeRmmInteriorDirectory,
            SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload,
            SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload,
            hready, hactive, List.append_assoc, Nat.add_assoc] at hcounted ⊢
  simpa using hdirect

structure ConcreteBPNativeSuccinctRMQFlatPayloadSegmentBacking
    (shape : Cartesian.CartesianShape) where
  source : ConcreteBPNativeSuccinctRMQFlatPayloadSource
  component : ConcreteBPNativeSuccinctRMQFlatPayloadComponent
  flatOffset : Nat
  componentOffset : Nat
  aliasesCountedPayload : Bool

def concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
  layout.componentFlatOffset
      (concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source) +
    concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
      shape source

theorem concreteBPNativeSuccinctRMQFlatPayloadSource_flat_slice
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hcounted :
      concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat
        shape source) :
    let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
    (layout.payload.drop
        (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset
          shape source)).take
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source).length =
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
        shape source := by
  let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
  let component :=
    concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source
  let sourcePayload :=
    concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source
  have hcomponent :
      (layout.payload.drop (layout.componentFlatOffset component)).take
          (layout.componentPayload component).length =
        layout.componentPayload component := by
    simpa [layout, component] using
      concreteBPNativeSuccinctRMQFlatPayloadLayout_component_slice
        shape component
  have hsource :
      ((layout.componentPayload component).drop
          (concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
            shape source)).take sourcePayload.length =
        sourcePayload := by
    simpa [layout, component, sourcePayload] using
      concreteBPNativeSuccinctRMQFlatPayloadSource_component_slice
        shape source hcounted
  simpa [layout, component, sourcePayload,
    concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset] using
    list_slice_trans layout.payload (layout.componentPayload component)
      sourcePayload (layout.componentFlatOffset component)
      (concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
        shape source) hcomponent hsource

def concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    ConcreteBPNativeSuccinctRMQFlatPayloadSegmentBacking shape :=
  { source := source
    component :=
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source
    flatOffset :=
      concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source
    componentOffset :=
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
        shape source
    aliasesCountedPayload :=
      concreteBPNativeSuccinctRMQFlatPayloadSourceAliasesCountedPayload
        source }

def concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking?
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    Option (ConcreteBPNativeSuccinctRMQFlatPayloadSegmentBacking shape) :=
  (concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment).map
    (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking shape)

def concreteBPNativeSuccinctRMQFlatPayloadReadStore
    (shape : Cartesian.CartesianShape) : WordRAM.ReadStore where
  readWord? segment index :=
    match concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment with
    | some source =>
        (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
          shape source)[index]?
    | none => none

theorem concreteBPNativeSuccinctRMQFlatPayloadReadStore_retiredFiniteSmallInterior_none
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 26 index =
        none /\
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 27 index =
        none := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadReadStore,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
    concreteBPNativeSuccinctRMQFlatPayloadSourceWords]

private theorem
    concreteBPNativeSummaryBaselineWords_eq_empty_of_not_active
    (shape : Cartesian.CartesianShape)
    (hnotActive :
      ¬ SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).baselineTable.store.words = #[] := by
  simp [SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical,
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
    SuccinctClose.canonicalBPRelativeSummaryBlockCount,
    SuccinctClose.canonicalBPRelativeSummarySuperCount,
    SuccinctClose.bpSuperblockBaselineEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    hnotActive]

private theorem
    concreteBPNativeSummaryMinRelWords_eq_empty_of_not_active
    (shape : Cartesian.CartesianShape)
    (hnotActive :
      ¬ SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).minRelTable.store.words = #[] := by
  simp [SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical,
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
    SuccinctClose.canonicalBPRelativeSummaryBlockCount,
    SuccinctClose.canonicalBPRelativeSummarySuperCount,
    SuccinctClose.bpBlockRelativeMinExcessEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    hnotActive]

private theorem
    concreteBPNativeSummaryMaxRelWords_eq_empty_of_not_active
    (shape : Cartesian.CartesianShape)
    (hnotActive :
      ¬ SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).maxRelTable.store.words = #[] := by
  simp [SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical,
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
    SuccinctClose.canonicalBPRelativeSummaryBlockCount,
    SuccinctClose.canonicalBPRelativeSummarySuperCount,
    SuccinctClose.bpBlockRelativeMaxExcessEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    hnotActive]

private theorem
    concreteBPNativeSummaryArgOffsetWords_eq_empty_of_not_active
    (shape : Cartesian.CartesianShape)
    (hnotActive :
      ¬ SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).argOffsetTable.store.words = #[] := by
  simp [SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical,
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
    SuccinctClose.canonicalBPRelativeSummaryBlockCount,
    SuccinctClose.canonicalBPRelativeSummarySuperCount,
    SuccinctClose.bpBlockArgMinLocalOffsetEntries,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    hnotActive]

def concreteBPNativeSuccinctRMQFlatPayloadReadSourceManifest
    (shape : Cartesian.CartesianShape)
    (segment index : Nat) (word : List Bool) : Prop :=
  exists source,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment =
        some source /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
        shape source)[index]? = some word /\
      SuccinctSpace.flattenPayloadWords
          (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
            shape source).toList =
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
        shape source).flatOffset =
          (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset
            ((concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
              shape source).component) +
            (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
              shape source).componentOffset /\
      ((concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
          shape source).aliasesCountedPayload = true ->
        (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape source).component =
          .bpCode /\
        (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape source).flatOffset = 0)

def concreteBPNativeSuccinctRMQFlatPayloadReadBacked
    (shape : Cartesian.CartesianShape)
    (segment index : Nat) (word : List Bool) : Prop :=
  exists source,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? segment =
        some source /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
        shape source)[index]? = some word /\
      SuccinctSpace.flattenPayloadWords
          (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
            shape source).toList =
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source /\
      concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat
        shape source /\
      (let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
       ((layout.componentPayload
            (concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source)).drop
          (concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset
            shape source)).take
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
            shape source).length =
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source) /\
      (let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
       (layout.payload.drop
          (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset
            shape source)).take
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
            shape source).length =
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
          shape source) /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
        shape source).flatOffset =
          (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset
            ((concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
              shape source).component) +
            (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
              shape source).componentOffset /\
      ((concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
          shape source).aliasesCountedPayload = true ->
        (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape source).component =
          .bpCode /\
        (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape source).flatOffset = 0)

theorem concreteBPNativeSuccinctRMQFlatPayloadSourceWords_erases
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    SuccinctSpace.flattenPayloadWords
        (concreteBPNativeSuccinctRMQFlatPayloadSourceWords
          shape source).toList =
      concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
        shape source := by
  cases source with
  | bpCode =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        SuccinctSpace.flattenPayloadWords_chunkPayloadWords
          (SuccinctRank.machineWordBits_pos shape.bpCode.length)
          shape.bpCode
  | selectSuperBaseOccurrence =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).baseOccurrenceTable.store.erases
  | selectSuperBaseWordIndex =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).baseWordIndexTable.store.erases
  | selectSuperRankBefore =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).rankBeforeTable.store.erases
  | selectSuperFirstOffset =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.superTable shape.bpCode false).firstOffsetTable.store.erases
  | selectLocalBaseOccurrence =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).baseOccurrenceTable.store.erases
  | selectLocalBaseWordIndex =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).baseWordIndexTable.store.erases
  | selectLocalRankBefore =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).rankBeforeTable.store.erases
  | selectLocalFirstOffset =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.localTable shape.bpCode false).firstOffsetTable.store.erases
  | selectLongFlagRankSuperTrue =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longFlagRankData
          shape.bpCode false).superTables.trueTable.store.erases
  | selectLongFlagRankBlockTrue =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longFlagRankData
          shape.bpCode false).blockTables.trueTable.store.erases
  | selectLongFlagBits =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longFlagRankData shape.bpCode false).bitWords.erases
  | selectLongRelative =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.longSuperRelativeTable shape.bpCode false).store.erases
  | selectSparseRankSuperTrue =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).rankData.superTables.trueTable.store.erases
  | selectSparseRankBlockTrue =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).rankData.blockTables.trueTable.store.erases
  | selectSparseFlagBits =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).rankData.bitWords.erases
  | selectSparseRelative =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        GenericSelect.sparseExceptionSelectData] using
        (GenericSelect.sparseExceptionDirectory
          shape.bpCode false).relativeTable.store.erases
  | finalRankSuperFalse =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.erases
  | finalRankBlockFalse =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.erases
  | finalRankBPCodeAlias =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (builtRelativeSplitBPCloseRankData shape).bitWords.erases
  | closeSummaryBaseline =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).baselineTable.store.erases
  | closeSummaryMinRel =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).minRelTable.store.erases
  | closeSummaryMaxRel =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).maxRelTable.store.erases
  | closeSummaryArgOffset =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).argOffsetTable.store.erases
  | closeInteriorLocal =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload] using
        (SuccinctClose.concreteBPRelativeRmmInteriorLocalTable
          shape).table.store.erases
  | closeInteriorGlobal =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
        concreteBPNativeSuccinctRMQFlatPayloadSourcePayload,
        SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload] using
        (SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable
          shape).table.store.erases
  | closeFiniteSmallInteriorMin =>
      change SuccinctSpace.flattenPayloadWords ([] : List (List Bool)) =
        ([] : List Bool)
      rfl
  | closeFiniteSmallInteriorArg =>
      change SuccinctSpace.flattenPayloadWords ([] : List (List Bool)) =
        ([] : List Bool)
      rfl
  | closeFiniteSmallSameBlock =>
      change SuccinctSpace.flattenPayloadWords ([] : List (List Bool)) =
        ([] : List Bool)
      rfl

theorem concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_flatOffset
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
        shape source).flatOffset =
      (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset
        ((concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
          shape source).component) +
        (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
          shape source).componentOffset := by
  rfl

theorem concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_alias
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
        shape source).aliasesCountedPayload = true ->
      (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
          shape source).component =
        .bpCode /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
          shape source).flatOffset = 0 := by
  cases source <;>
    simp [concreteBPNativeSuccinctRMQFlatPayloadSourceBacking,
      concreteBPNativeSuccinctRMQFlatPayloadSourceAliasesCountedPayload,
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponent,
      concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset,
      ConcreteBPNativeSuccinctRMQFlatPayloadLayout.componentFlatOffset,
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset]

/--
Any concrete segment backing exposed by the flat manifest carries the same
component/offset equation as its source, and an alias flag can only point back
to the already-counted BP-code component.
-/
theorem concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking_offsets
    (shape : Cartesian.CartesianShape)
    {segment : Nat}
    {backing : ConcreteBPNativeSuccinctRMQFlatPayloadSegmentBacking shape}
    (h :
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape segment =
        some backing) :
    backing.flatOffset =
        (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset
          backing.component + backing.componentOffset /\
      (backing.aliasesCountedPayload = true ->
        backing.component = .bpCode /\ backing.flatOffset = 0) := by
  unfold concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? at h
  cases hsource :
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
        segment with
  | none =>
      simp [hsource] at h
  | some source =>
      rw [hsource] at h
      injection h with hbacking
      subst backing
      constructor
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_flatOffset
            shape source
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_alias
            shape source

theorem concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_source_manifest
    (shape : Cartesian.CartesianShape)
    {segment index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
          segment index = some word) :
    concreteBPNativeSuccinctRMQFlatPayloadReadSourceManifest
      shape segment index word := by
  unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
  unfold concreteBPNativeSuccinctRMQFlatPayloadReadSourceManifest
  cases hsource :
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
        segment with
  | none =>
      simp [hsource] at hread
  | some source =>
      refine ⟨source, rfl, ?_, ?_, ?_, ?_⟩
      · simpa [hsource] using hread
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceWords_erases
            shape source
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_flatOffset
            shape source
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_alias
            shape source

theorem concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_read_backed
    (shape : Cartesian.CartesianShape)
    {segment index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
          segment index = some word)
    (hcounted :
      concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
        shape segment) :
    concreteBPNativeSuccinctRMQFlatPayloadReadBacked
      shape segment index word := by
  unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
  unfold concreteBPNativeSuccinctRMQFlatPayloadReadBacked
  cases hsource :
      concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
        segment with
  | none =>
      simp [hsource] at hread
  | some source =>
      have hsourceCounted :
          concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat
            shape source := by
        simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
          hsource] using hcounted
      refine ⟨source, rfl, ?_, ?_, hsourceCounted, ?_, ?_, ?_, ?_⟩
      · simpa [hsource] using hread
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceWords_erases
            shape source
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSource_component_slice
            shape source hsourceCounted
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSource_flat_slice
            shape source hsourceCounted
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_flatOffset
            shape source
      · exact
          concreteBPNativeSuccinctRMQFlatPayloadSourceBacking_alias
            shape source

/--
Every successful read from the concrete flat read-store has a source manifest:
it names the concrete source table, records the source word lookup, and keeps
the component/offset equation. This is not, by itself, a counted-payload
containment theorem for finite-small sources.
-/
theorem
    concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_reads_have_source_manifest
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload =
        concreteBPNativeSuccinctRMQPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape /\
      (let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
       layout.payload =
        layout.bpCodePayload ++ layout.accessRankPayload ++
          layout.selectPayload ++ layout.accessPadding ++
            layout.closePayload ++ layout.closePadding) /\
      (forall {segment index : Nat} {word : List Bool},
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
            segment index = some word ->
          concreteBPNativeSuccinctRMQFlatPayloadReadSourceManifest
            shape segment index word) := by
  constructor
  · exact concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_eq shape
  constructor
  · exact concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_components shape
  · intro segment index word hread
    exact
      concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_source_manifest
        shape hread

/--
Successful reads from sources known to be counted in the current flat payload
are positionally backed by that payload. The counted-source precondition is
essential for legacy finite-small interior segments `26` and `27`: their source
names are retained for compatibility, but they are not counted in `closePayload`
and the public all-size trace proves no successful reads to them.
-/
theorem
    concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_reads_backed_by_counted_payload
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload =
        concreteBPNativeSuccinctRMQPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape /\
      (let layout := concreteBPNativeSuccinctRMQFlatPayloadLayout shape
       layout.payload =
        layout.bpCodePayload ++ layout.accessRankPayload ++
          layout.selectPayload ++ layout.accessPadding ++
            layout.closePayload ++ layout.closePadding) /\
      (forall {segment index : Nat} {word : List Bool},
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
            segment index = some word ->
          concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
            shape segment ->
          concreteBPNativeSuccinctRMQFlatPayloadReadBacked
            shape segment index word) := by
  constructor
  · exact concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_eq shape
  constructor
  · exact concreteBPNativeSuccinctRMQFlatPayloadLayout_payload_components shape
  · intro segment index word hread hcounted
    exact
      concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_read_backed
        shape hread hcounted

/--
A successful flat-store read is counted once the branch predicates required by
conditional close sources are discharged: summary segments `20` through `23`
require the canonical summary table to be active, local/global interior segments
`24` and `25` require Ready. Retired all-pairs interior slots `26` and `27`
are physically empty and cannot satisfy the successful-read premise.
-/
theorem
    concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted
    (shape : Cartesian.CartesianShape)
    {segment index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
          segment index = some word)
    (h24 : segment = 24 ->
      SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (h25 : segment = 25 ->
      SuccinctClose.concreteBPRelativeRmmInteriorReady shape) :
    concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
      shape segment := by
  match segment with
  | 0 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 1 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 2 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 3 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 4 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 5 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 6 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 7 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 8 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 9 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 10 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 11 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 12 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 13 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 14 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 15 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 16 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 17 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 18 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 19 =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat]
  | 20 =>
      by_cases hactive :
          SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
          concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat] using
          hactive
      · unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
        have hwords :=
          concreteBPNativeSummaryBaselineWords_eq_empty_of_not_active
            shape hactive
        simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
          hwords] at hread
  | 21 =>
      by_cases hactive :
          SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
          concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat] using
          hactive
      · unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
        have hwords :=
          concreteBPNativeSummaryMinRelWords_eq_empty_of_not_active
            shape hactive
        simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
          hwords] at hread
  | 22 =>
      by_cases hactive :
          SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
          concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat] using
          hactive
      · unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
        have hwords :=
          concreteBPNativeSummaryMaxRelWords_eq_empty_of_not_active
            shape hactive
        simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
          hwords] at hread
  | 23 =>
      by_cases hactive :
          SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape
      · simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
          concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat] using
          hactive
      · unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
        have hwords :=
          concreteBPNativeSummaryArgOffsetWords_eq_empty_of_not_active
            shape hactive
        simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
          concreteBPNativeSuccinctRMQFlatPayloadSourceWords,
          hwords] at hread
  | 24 =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat] using
        h24 rfl
  | 25 =>
      simpa [concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat,
        concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat] using
        h25 rfl
  | 26 =>
      unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceWords] at hread
  | 27 =>
      unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceWords] at hread
  | 28 =>
      unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
        concreteBPNativeSuccinctRMQFlatPayloadSourceWords] at hread
  | _ + 29 =>
      unfold concreteBPNativeSuccinctRMQFlatPayloadReadStore at hread
      simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?] at hread

theorem
    concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted_of_not_ready
    (shape : Cartesian.CartesianShape)
    (_hnotReady : ¬ SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    {segment index : Nat} {word : List Bool}
    (h24 : segment ≠ 24)
    (h25 : segment ≠ 25)
    (hread :
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
          segment index = some word) :
    concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
      shape segment :=
  concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted
    shape hread
    (fun hseg => False.elim (h24 hseg))
    (fun hseg => False.elim (h25 hseg))

def concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked
    (shape : Cartesian.CartesianShape) :
    WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment index (some word) =>
      concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
        shape segment /\
        concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          shape segment index word
  | _ => True

def concreteBPNativeSuccinctRMQTraceEventNoFiniteSmallInteriorSuccessfulRead :
    WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord 26 _ (some _) => False
  | WordRAM.TraceEvent.readWord 27 _ (some _) => False
  | _ => True

def concreteBPNativeSuccinctRMQTraceEventNoReadyCloseSuccessfulRead :
    WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord 24 _ (some _) => False
  | WordRAM.TraceEvent.readWord 25 _ (some _) => False
  | _ => True

theorem
    concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked_of_flatStore_match
    (shape : Cartesian.CartesianShape)
    {event : WordRAM.TraceEvent}
    (hmatch :
      event.matchesReadStore
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape))
    (h24 :
      forall index word,
        event = WordRAM.TraceEvent.readWord 24 index (some word) ->
          SuccinctClose.concreteBPRelativeRmmInteriorReady shape)
    (h25 :
      forall index word,
        event = WordRAM.TraceEvent.readWord 25 index (some word) ->
          SuccinctClose.concreteBPRelativeRmmInteriorReady shape) :
    concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked
      shape event := by
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked]
      | some word =>
          have hread :
              (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
                  segment index = some word := by
            simpa [WordRAM.TraceEvent.matchesReadStore] using hmatch
          have hcounted :
              concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
                shape segment :=
            concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_read_segment_counted
              shape hread
              (fun hseg => h24 index word (by cases hseg; rfl))
              (fun hseg => h25 index word (by cases hseg; rfl))
          exact
            ⟨hcounted,
              concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_read_backed
                shape hread hcounted⟩
  | wordRank target limit result =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked]
  | wordSelect target occurrence result =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked]
  | syntheticCostOnlyPrimitive =>
      simp [concreteBPNativeSuccinctRMQFlatPayloadTraceEventSuccessfulReadBacked]

def concreteBPNativeSuccinctRMQFlatPayloadSegmentBackingsAll
    (shape : Cartesian.CartesianShape) : Prop :=
    concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 0 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .bpCode) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 1 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSuperBaseOccurrence) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 2 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSuperBaseWordIndex) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 3 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSuperRankBefore) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 4 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSuperFirstOffset) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 5 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLocalBaseOccurrence) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 6 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLocalBaseWordIndex) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 7 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLocalRankBefore) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 8 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLocalFirstOffset) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 9 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLongFlagRankSuperTrue) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 10 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLongFlagRankBlockTrue) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 11 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLongFlagBits) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 12 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectLongRelative) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 13 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSparseRankSuperTrue) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 14 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSparseRankBlockTrue) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 15 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSparseFlagBits) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 16 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .selectSparseRelative) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 17 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .finalRankSuperFalse) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 18 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .finalRankBlockFalse) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 19 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .finalRankBPCodeAlias) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 20 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeSummaryBaseline) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 21 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeSummaryMinRel) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 22 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeSummaryMaxRel) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 23 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeSummaryArgOffset) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 24 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeInteriorLocal) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 25 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeInteriorGlobal) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 26 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeFiniteSmallInteriorMin) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 27 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeFiniteSmallInteriorArg) /\
      concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking? shape 28 =
        some
          (concreteBPNativeSuccinctRMQFlatPayloadSourceBacking
            shape .closeFiniteSmallSameBlock)

theorem concreteBPNativeSuccinctRMQFlatPayloadSegmentBackings_all
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQFlatPayloadSegmentBackingsAll shape := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSegmentBackingsAll,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentBacking?,
    concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?]

theorem concreteBPNativeSuccinctRMQFlatPayloadReadStore_eq_global
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
        segment index =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        segment index := by
  match segment with
  | 0 =>
      rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
      rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | 17 => rfl
  | 18 => rfl
  | 19 => rfl
  | 20 => rfl
  | 21 => rfl
  | 22 => rfl
  | 23 => rfl
  | 24 => rfl
  | 25 => rfl
  | 26 => rfl
  | 27 => rfl
  | 28 => rfl
  | _ + 29 => rfl

end SuccinctFinal
end RMQ

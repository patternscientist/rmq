import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceFactorization
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Payload
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Header
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Space
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Address
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram

/-!
# Exact-type consumers for the EG-CP packed cell-probe candidate

Every declaration below writes out the proposition or signature it depends on in
full and then discharges it with the corresponding library result. The point is
that the expected type is stated here, independently of the current declaration in
the library modules, so weakening a library theorem breaks this file rather than
silently adapting to it.

`#print axioms` over a theorem's current type does not do this: it reports what the
declaration happens to say now. These consumers say what it must say.

This file is the validation root for the falsification gate. It currently pins:

* the raw payload identity (`FG-01`);
* the shape-free source/address factorization (`FG-02`, `FG-03`);
* the `K = 1` header schema, including the two shapes of size two (`FG-04`);
* the packed memory, its round trip and its cell arity (`FG-05`);
* the allocated-space bound and its residual (`FG-06`);
* the bit-address surface and the conditional physical probe plan, with
  allocation, coverage, decoding, charged probe count and boundary instances
  (towards `FG-08`, `FG-09`).

The controller, whole-run lowering, same-run correctness, liveness and the
committed replay are not stated here because they do not yet exist, and a
consumer for an absent theorem would be a placeholder rather than a check.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe
namespace Validation

open RMQ.Cartesian

/-! ### `FG-01`: the stored payload is the canonical object

A length agreement is compatible with a structurally equal sibling payload; an
identity is not. These consumers state the identity, so replacing the stored
bits by a separately defined copy of the same shape breaks this file.
-/

/--
Pins that the bits the packed representation stores are the canonical flat RMQ
payload, named at its existing definition site with its existing access family.
-/
theorem packedPayloadIsCanonicalObject :
    forall shape : CartesianShape,
      packedPayloadBits shape =
        concreteBPNativeSuccinctRMQPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape :=
  packedPayloadBits_eq_canonical

/-- The same identity at the list-facing front door. -/
theorem packedListPayloadIsCanonicalObject :
    forall xs : List Int,
      packedPayloadBitsOfList xs =
        concreteBPNativeSuccinctRMQPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily
          (Cartesian.shape xs) :=
  packedPayloadBitsOfList_eq_canonical

/--
Pins that the serialized string is the header cell followed by that payload and
nothing else: dropping one cell recovers the payload object exactly, so there is
no room for a second table between them.
-/
theorem packedSerializedIsHeaderThenCanonicalPayload :
    forall shape : CartesianShape,
      (packedSerializedBits shape).drop (packedCellWidth shape.size) =
        packedPayloadBits shape :=
  packedSerializedBits_drop_header

/-! ### The factorization surface is shape-free -/

/--
Pins the signature. The address function takes the input size, the decoded long
count and a typed source, and returns a bit offset.

Adding a `CartesianShape` parameter, or any parameter carrying shape content,
makes this ascription fail. That is the entire content of "shape-free": it is a
statement about the type, checked by the elaborator.
-/
def packedSourceComponentOffsetSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  packedSourceComponentOffset

/-- Pins the counting guard's signature as a decidable predicate on the size. -/
def packedInteriorReadySignature : Nat -> Prop :=
  PackedInteriorReady

instance : forall n : Nat, Decidable (packedInteriorReadySignature n) :=
  packedInteriorReadyDecidable

/-! ### The factorization agrees with the canonical layout -/

/--
Pins `FG-02`'s within-component conclusion at its exact objects: the canonical
shape-indexed offset, the shape-free offset, the input size, and the long count.

Weakening the library theorem to a congruence, restricting it to a subset of
sources, or adding a hypothesis all break this consumer.
-/
theorem packedSourceComponentOffsetAgrees :
    forall (shape : CartesianShape)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset shape source =
        packedSourceComponentOffset shape.size (longCount shape) source :=
  packedSourceComponentOffset_eq

/--
Pins `FG-03`'s close-base conclusion, including that the right-hand side is a
function of the size alone.
-/
theorem packedCloseComponentBaseIsSizeOnly :
    forall shape : CartesianShape,
      (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset
          .closePayload =
        2 * shape.size + packedAccessOverhead shape.size :=
  closeComponent_flatOffset

/--
Pins `FG-03`'s terminality clause: the canonical select payload is a prefix that
does not mention the sparse relative table, followed by that table.
-/
theorem packedSparseRelativeIsTerminal :
    forall shape : CartesianShape,
      (GenericSelect.sparseExceptionSelectSource shape.bpCode false).payload =
        packedSelectPrefixBits shape ++
          (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload :=
  selectPayload_eq_prefix_append_sparseRelative

/-- Pins the addressing consequence of terminality. -/
theorem packedSelectOffsetsStayInPrefix :
    forall (shape : CartesianShape)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
      concreteBPNativeSuccinctRMQFlatPayloadSourceComponent source =
          .selectPayload ->
        concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset shape source <=
          (packedSelectPrefixBits shape).length :=
  selectSourceComponentOffset_le_prefix

/--
Pins the counting guard's agreement with the canonical predicate.

This is the theorem a controller needs before issuing the two close-interior
reads, whose canonical offsets are computed unconditionally but are only inside
the component when the interior is ready.
-/
theorem packedSourceCountedAgrees :
    forall (shape : CartesianShape)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
      concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat shape source <->
        PackedSourceCounted shape.size source :=
  sourceCounted_iff_packed

/--
Pins the long-count term at its exact factors.

This is the statement that makes `K = 1` the candidate header rather than `K = 0`:
the long relative table's length is the long count times two size-only factors.
-/
theorem packedLongRelativeLengthIsLongCountTimesSizeOnly :
    forall shape : CartesianShape,
      (GenericSelect.longSuperRelativeTable shape.bpCode false).payload.length =
        longCount shape *
          (GenericSelect.superStride (2 * shape.size) *
            GenericSelect.wordBits (2 * shape.size)) :=
  longSuperRelativeTable_length_eq

/--
Pins the whole flat address, not just the within-component part: component base
plus offset, both computed from the size and the decoded long count alone.
-/
def packedSourceFlatOffsetSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  packedSourceFlatOffset

theorem packedSourceFlatOffsetAgrees :
    forall (shape : CartesianShape)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
      concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source =
        packedSourceFlatOffset shape.size (longCount shape) source :=
  packedSourceFlatOffset_eq

/-! ### The `K = 1` header -/

/-- Pins `P` and `w` as functions of the input size alone. -/
def packedPayloadLengthSignature : Nat -> Nat := packedPayloadLength

def packedCellWidthSignature : Nat -> Nat := packedCellWidth

/-- Pins that the canonical payload's length is that size-only function. -/
theorem packedPayloadLengthIsSizeOnly :
    forall shape : CartesianShape,
      (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload.length =
        packedPayloadLength shape.size :=
  packedPayloadLength_eq

/--
Pins the all-size count fit with no size side condition. A version guarded by a
threshold would fail this ascription.
-/
theorem packedLongCountFitsOneCell :
    forall shape : CartesianShape,
      longCount shape < 2 ^ packedCellWidth shape.size :=
  longCount_lt_two_pow_width

/-- Pins exact one-cell header arity. -/
theorem packedHeaderIsExactlyOneCell :
    forall shape : CartesianShape,
      (packedHeaderBits shape).length = packedCellWidth shape.size :=
  packedHeaderBits_length

/-- Pins that decoding the header recovers the long count exactly. -/
theorem packedHeaderDecodes :
    forall shape : CartesianShape,
      SuccinctSpace.bitsToNatLE (packedHeaderBits shape) = longCount shape :=
  packedHeaderBits_decode

/-! ### Packed memory and allocated space -/

/-- Pins the memory round trip: the cells recover the padded bits exactly. -/
theorem packedMemoryRoundTrips :
    forall shape : CartesianShape,
      (packedMemory shape).flatten = packedPaddedBits shape :=
  packedMemory_flatten

/-- Pins that every allocated cell is exactly one full width, none short. -/
theorem packedMemoryCellsAreFullWidth :
    forall (shape : CartesianShape) {cell : List Bool},
      cell ∈ packedMemory shape -> cell.length = packedCellWidth shape.size :=
  fun shape _ h => packedMemory_cell_length shape h

/--
Pins the space bound at allocated cells times width, over the same `packedMemory`
the execution is meant to probe, not over the number of meaningful bits.
-/
theorem packedAllocatedSpaceBound :
    forall shape : CartesianShape,
      (packedMemory shape).length * packedCellWidth shape.size <=
        2 * shape.size + packedRho shape.size :=
  packedMemory_length_mul_width_le

/--
Pins the cell-crossing bound: any span of at most one cell width is a slice of two
consecutive cells. This is the two-probes-per-logical-word bound.
-/
theorem packedSpanNeedsAtMostTwoCells :
    forall (shape : CartesianShape) (p width : Nat),
      width <= packedCellWidth shape.size ->
        ((packedPaddedBits shape).drop p).take width =
          ((packedCellAt shape (p / packedCellWidth shape.size) ++
              packedCellAt shape (p / packedCellWidth shape.size + 1)).drop
                (p % packedCellWidth shape.size)).take width :=
  packedSpan_from_two_cells

/-- Pins that the residual is little-o linear. -/
theorem packedRhoIsLittleOLinear : SuccinctSpace.LittleOLinear packedRho :=
  packedRho_littleO

/-! ### `FG-04` at size two

Size two is the smallest size carrying more than one shape, so it is the
smallest case that can tell "the width is a function of the input size" apart
from "the widths tried so far happened to agree". Both shapes are pinned, and
both are required to have arity `packedCellWidth 2` — the same numeral at the
same size.
-/

theorem packedSizeTwoShapesDiffer :
    Not (packedSizeTwoLeft = packedSizeTwoRight) := by
  intro h
  exact CartesianShape.noConfusion h fun hleft _ =>
    CartesianShape.noConfusion hleft

theorem packedSizeTwoLeftHasSizeTwo : packedSizeTwoLeft.size = 2 := rfl

theorem packedSizeTwoRightHasSizeTwo : packedSizeTwoRight.size = 2 := rfl

theorem packedSizeTwoLeftHeaderIsExactlyOneCell :
    (packedHeaderBits packedSizeTwoLeft).length = packedCellWidth 2 :=
  packedHeaderBits_length packedSizeTwoLeft

theorem packedSizeTwoRightHeaderIsExactlyOneCell :
    (packedHeaderBits packedSizeTwoRight).length = packedCellWidth 2 :=
  packedHeaderBits_length packedSizeTwoRight

theorem packedSizeTwoLeftHeaderDecodes :
    SuccinctSpace.bitsToNatLE (packedHeaderBits packedSizeTwoLeft) =
      longCount packedSizeTwoLeft :=
  packedHeaderBits_decode packedSizeTwoLeft

theorem packedSizeTwoRightHeaderDecodes :
    SuccinctSpace.bitsToNatLE (packedHeaderBits packedSizeTwoRight) =
      longCount packedSizeTwoRight :=
  packedHeaderBits_decode packedSizeTwoRight

theorem packedSizeTwoLeftCountFitsOneCell :
    longCount packedSizeTwoLeft < 2 ^ packedCellWidth 2 :=
  longCount_lt_two_pow_width packedSizeTwoLeft

theorem packedSizeTwoRightCountFitsOneCell :
    longCount packedSizeTwoRight < 2 ^ packedCellWidth 2 :=
  longCount_lt_two_pow_width packedSizeTwoRight

theorem packedSizeTwoLeftPayloadLengthIsSizeOnly :
    (packedPayloadBits packedSizeTwoLeft).length = packedPayloadLength 2 :=
  packedPayloadBits_length packedSizeTwoLeft

theorem packedSizeTwoRightPayloadLengthIsSizeOnly :
    (packedPayloadBits packedSizeTwoRight).length = packedPayloadLength 2 :=
  packedPayloadBits_length packedSizeTwoRight

/-! ### The bit-address surface

The address arithmetic a probe-only controller would run. Pinned here so that
reintroducing a shape argument, or letting a payload address forget the header
cell, breaks this file.
-/

/--
Pins the address signature. Input size, decoded long count, typed source, index
and width; no shape, no list, no proof argument.
-/
def packedBitAddressSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource ->
      Nat -> Nat -> Nat :=
  packedBitAddress

/-- Pins that a payload address is the flat address shifted by one header cell. -/
theorem packedBitAddressShiftsByExactlyOneCell :
    forall (n longCount : Nat)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
      (index width : Nat),
      packedBitAddress n longCount source index width =
        packedCellWidth n +
          (packedSourceFlatOffset n longCount source + index * width) :=
  packedBitAddress_eq

/-- Pins that the payload really does sit one cell into the packed bit string. -/
theorem packedPayloadSitsOneCellIn :
    forall (shape : CartesianShape) (j width : Nat),
      j + width <= packedPayloadLength shape.size ->
        ((packedPaddedBits shape).drop
            (packedCellWidth shape.size + j)).take width =
          ((packedPayloadBits shape).drop j).take width :=
  packedPayloadSlice

/-! ### The conditional physical probe plan

`FG-08` and `FG-09` need a plan that issues real addresses. The consumers below
pin allocation, coverage, decoding and the charged count, and they pin the two
boundary facts that make the conditional plan different from the unconditional
pair it replaced.
-/

/-- Pins the plan's signature: input size, bit address, width. -/
def packedProbePlanSignature : Nat -> Nat -> Nat -> List Nat :=
  packedProbePlan

/-- Pins that the charged probe count is the issued plan's length. -/
theorem packedProbeCountIsPlanLength :
    forall n bit width : Nat,
      packedProbeCount n bit width = (packedProbePlan n bit width).length :=
  fun _ _ _ => rfl

/--
Pins that every issued address is allocated. This is the clause the
unconditional two-cell plan could not supply.
-/
theorem packedProbeAddressesAreAllocated :
    forall {n bit width addr : Nat},
      bit + width <= packedAllocatedBits n ->
        addr ∈ packedProbePlan n bit width ->
          addr < packedCellCount n :=
  packedProbePlan_lt_cellCount

/-- Pins that the issued plan fetches successfully against the packed memory. -/
theorem packedProbeFetchSucceeds :
    forall (shape : CartesianShape) (bit width : Nat),
      bit + width <= packedAllocatedBits shape.size ->
        packedFetch (packedMemory shape)
            (packedProbePlan shape.size bit width) =
          some ((packedProbePlan shape.size bit width).map
            (packedCellAt shape)) :=
  fun shape _ _ hfit => packedFetch_plan shape hfit

/-- Pins that the issued cells cover the whole requested bit range. -/
theorem packedProbeCoversRequestedRange :
    forall n bit width : Nat,
      width <= packedCellWidth n ->
        width <=
          packedProbeCount n bit width * packedCellWidth n -
            bit % packedCellWidth n :=
  packedProbe_covers_range

/-- Pins that decoding the fetched cells reproduces the requested window. -/
theorem packedProbeDecodesExactly :
    forall (shape : CartesianShape) (bit width : Nat),
      width <= packedCellWidth shape.size ->
        bit + width <= packedAllocatedBits shape.size ->
          (packedFetch (packedMemory shape)
                (packedProbePlan shape.size bit width)).map
              (packedDecodeSpan shape.size bit width) =
            some (((packedPaddedBits shape).drop bit).take width) :=
  fun shape _ _ hwidth hfit => packedProbePlan_decode shape hwidth hfit

/-- Pins the per-read probe cap at two cells. -/
theorem packedProbeCountAtMostTwo :
    forall n bit width : Nat, packedProbeCount n bit width <= 2 :=
  packedProbeCount_le_two

/--
Pins that a typed source read decodes to exactly the canonical payload slice,
addressed only through the size, the decoded long count, the source, the index
and the width.
-/
theorem packedSourceReadDecodesToCanonicalSlice :
    forall (shape : CartesianShape)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
      (index width : Nat),
      width <= packedCellWidth shape.size ->
        concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
              index * width + width <=
            packedPayloadLength shape.size ->
          (packedFetch (packedMemory shape)
                (packedSourceProbePlan shape.size (longCount shape) source index
                  width)).map
              (packedDecodeSpan shape.size
                (packedBitAddress shape.size (longCount shape) source index
                  width)
                width) =
            some
              (((packedPayloadBits shape).drop
                  (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape
                      source +
                    index * width)).take width) :=
  fun shape source index width hwidth hfit =>
    packedSourceRead_decode shape source index width hwidth hfit

/-! #### The logical address side is already shape-free

A logical read of the flat payload store is a pair `(segment, index)`. The
consumers below pin that turning that pair into a typed source, and then into a
physical probe plan, needs no shape. The width remains an explicit argument; the
mirror that would derive it from `(n, longCount, segment)` does not exist yet and
is not pinned here.
-/

/-- Pins the segment-to-source map's shape-free signature. -/
def packedSegmentSourceSignature :
    Nat -> Option ConcreteBPNativeSuccinctRMQFlatPayloadSource :=
  packedSegmentSource?

/-- Pins the logical probe plan's shape-free signature. -/
def packedLogicalProbePlanSignature :
    Nat -> Nat -> Nat -> Nat -> Nat -> List Nat :=
  packedLogicalProbePlan

/-- Pins the per-logical-read probe bound. -/
theorem packedLogicalReadIssuesAtMostTwoProbes :
    forall n longCount segment index width : Nat,
      (packedLogicalProbePlan n longCount segment index width).length <= 2 :=
  packedLogicalProbePlan_length_le_two

/-- Pins that a logical read decodes to the canonical payload slice. -/
theorem packedLogicalReadDecodesToCanonicalSlice :
    forall (shape : CartesianShape) (segment : Nat)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
      (index width : Nat),
      packedSegmentSource? segment = some source ->
        width <= packedCellWidth shape.size ->
          concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape source +
                index * width + width <=
              packedPayloadLength shape.size ->
            (packedFetch (packedMemory shape)
                  (packedLogicalProbePlan shape.size (longCount shape) segment
                    index width)).map
                (packedDecodeSpan shape.size
                  (packedBitAddress shape.size (longCount shape) source index
                    width)
                  width) =
              some
                (((packedPayloadBits shape).drop
                    (concreteBPNativeSuccinctRMQFlatPayloadSourceFlatOffset shape
                        source +
                      index * width)).take width) :=
  fun shape _ _ index width hsource hwidth hfit =>
    packedLogicalRead_decode shape index width hsource hwidth hfit

/-! #### A logical read carries no table content

`FG-07` forbids the controller from receiving shape-derived data. The existing
supplied-store leaves do take such data, so the question is whether it is
load-bearing for the **replies** or only for the **geometry**. These consumers pin
the answer at the entry-table level: it is only the geometry.
-/

/--
Pins that a fixed-width table's read program is an index and nothing else. The
two tables share no parameter, so the program cannot transport stored data.
-/
theorem packedTableReadIsAnIndexNotALookup :
    forall {entriesLeft entriesRight : List Nat} {widthLeft widthRight : Nat}
      (tableLeft : SuccinctSpace.FixedWidthNatTable entriesLeft widthLeft)
      (tableRight : SuccinctSpace.FixedWidthNatTable entriesRight widthRight)
      (index : Nat),
      tableLeft.readProgram index = tableRight.readProgram index :=
  fun tableLeft tableRight index =>
    packedTableReadProgram_content_free tableLeft tableRight index

/--
Pins that the four-field select entry read against a supplied store is the same
trace result for unrelated tables: same reads, same order, same replies, same
decoded entry. This is what makes the remaining `FG-07` work a factorization of
geometry scalars rather than a change of architecture.
-/
theorem packedSelectEntryReadIsDeterminedByTheStore :
    forall {entriesLeft entriesRight :
        List GenericSelect.SparseDenseSelectDenseLocalEntry}
      {widthLeft widthRight : Nat}
      (tableLeft :
        GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
          entriesLeft widthLeft)
      (tableRight :
        GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
          entriesRight widthRight)
      (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
      (store : WordRAM.ReadStore) (index : Nat),
      tableLeft.readTraceResultRelabeledWithStore layout store index =
        tableRight.readTraceResultRelabeledWithStore layout store index :=
  fun tableLeft tableRight layout store index =>
    packedSelectEntryRead_content_free tableLeft tableRight layout store index

/-! #### The select leaf's geometry is size-only

The four scalars `bpChunkedSelectTraceResultWithStore` consumes from the select
data record, and its validity guard, are pinned here as functions of the input
size alone. With the content-free theorems above, that is the whole select-side
shape-dependence except `queryOccurrence`, which is not pinned because it is not
mirrored.
-/

def packedSelectWordSizeSignature : Nat -> Nat := packedSelectWordSize

def packedSelectSuperStrideSignature : Nat -> Nat := packedSelectSuperStride

def packedSelectLocalStrideSignature : Nat -> Nat := packedSelectLocalStride

def packedSelectLocalSlotsPerSuperSignature : Nat -> Nat :=
  packedSelectLocalSlotsPerSuper

theorem packedSelectWordSizeIsSizeOnly :
    forall shape : CartesianShape,
      (GenericSelect.sparseExceptionSelectData shape.bpCode false).wordSize =
        packedSelectWordSize shape.size :=
  packedSelectWordSize_eq

theorem packedSelectSuperStrideIsSizeOnly :
    forall shape : CartesianShape,
      (GenericSelect.sparseExceptionSelectData shape.bpCode false).superStride =
        packedSelectSuperStride shape.size :=
  packedSelectSuperStride_eq

theorem packedSelectLocalStrideIsSizeOnly :
    forall shape : CartesianShape,
      (GenericSelect.sparseExceptionSelectData shape.bpCode false).localStride =
        packedSelectLocalStride shape.size :=
  packedSelectLocalStride_eq

theorem packedSelectLocalSlotsPerSuperIsSizeOnly :
    forall shape : CartesianShape,
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).localSlotsPerSuper =
        packedSelectLocalSlotsPerSuper shape.size :=
  packedSelectLocalSlotsPerSuper_eq

/--
Pins that the select leaf's validity dispatch is `idx < n`: evaluable from the
input size alone, with no header field and no probe.
-/
theorem packedSelectValidityGuardIsTheInputSize :
    forall shape : CartesianShape,
      GenericSelect.occurrenceCount shape.bpCode false = shape.size :=
  packedSelectOccurrenceCount_eq_size

/--
Pins the last select-side scalar: the queried occurrence is a function of the
index alone. The two records share no parameter, so it cannot be transporting
anything derived from the shape.
-/
theorem packedSelectQueryOccurrenceIsTheIndexAlone :
    forall {bitsLeft bitsRight : List Bool} {targetLeft targetRight : Bool}
      {superLeft blockLeft superRight blockRight : Nat}
      (dataLeft :
        GenericSelect.SparseExceptionSelectData
          bitsLeft targetLeft superLeft blockLeft)
      (dataRight :
        GenericSelect.SparseExceptionSelectData
          bitsRight targetRight superRight blockRight)
      (index : Nat),
      dataLeft.queryOccurrence index = dataRight.queryOccurrence index :=
  fun dataLeft dataRight index =>
    packedSelectQueryOccurrence_content_free dataLeft dataRight index

/-- Pins that the dense two-word select read carries no bit-store content. -/
theorem packedDenseTwoWordSelectReadIsDeterminedByTheStore :
    forall {bitsLeft bitsRight : List Bool} {wordSize : Nat}
      (bitWordsLeft : SuccinctSpace.BoundedPayloadWordStore bitsLeft wordSize)
      (bitWordsRight : SuccinctSpace.BoundedPayloadWordStore bitsRight wordSize)
      (bitWordSegment rankTableSegment selectTableSegment chunkBits : Nat)
      (target : Bool) (store : WordRAM.ReadStore)
      (basePosition baseOccurrence occurrence : Nat),
      GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
          bitWordSegment rankTableSegment selectTableSegment chunkBits target
          bitWordsLeft store basePosition baseOccurrence occurrence =
        GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
          bitWordSegment rankTableSegment selectTableSegment chunkBits target
          bitWordsRight store basePosition baseOccurrence occurrence :=
  fun bitWordsLeft bitWordsRight bitWordSegment rankTableSegment
      selectTableSegment chunkBits target store basePosition baseOccurrence
      occurrence =>
    packedDenseTwoWordSelectRead_content_free bitWordsLeft bitWordsRight
      bitWordSegment rankTableSegment selectTableSegment chunkBits target store
      basePosition baseOccurrence occurrence

/--
Pins that the two-level rank read is determined by three scalars. The two records
are over unrelated bit strings with unrelated overheads and unrelated query
costs; agreeing on `queryPos pos`, `wordSize` and `blocksPerSuper` is enough.
-/
theorem packedRankReadIsDeterminedByThreeScalars :
    forall {bitsLeft bitsRight : List Bool}
      {superLeft blockLeft queryLeft superRight blockRight queryRight : Nat}
      (dataLeft :
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
          bitsLeft superLeft blockLeft queryLeft)
      (dataRight :
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
          bitsRight superRight blockRight queryRight)
      (store : WordRAM.ReadStore)
      (superSegment blockSegment wordSegment chunkSegment chunkBits : Nat)
      (target : Bool) (pos : Nat),
      dataLeft.queryPos pos = dataRight.queryPos pos ->
        dataLeft.wordSize = dataRight.wordSize ->
          dataLeft.blocksPerSuper = dataRight.blocksPerSuper ->
            dataLeft.bpChunkedRankTraceResultWithStore store superSegment
                blockSegment wordSegment chunkSegment chunkBits target pos =
              dataRight.bpChunkedRankTraceResultWithStore store superSegment
                blockSegment wordSegment chunkSegment chunkBits target pos :=
  fun dataLeft dataRight store superSegment blockSegment wordSegment
      chunkSegment chunkBits target pos hquery hwordSize hblocks =>
    packedRankRead_scalar_determined dataLeft dataRight store superSegment
      blockSegment wordSegment chunkSegment chunkBits target pos hquery
      hwordSize hblocks

/-! #### A record-free select entry read exists

The content-free theorems say the record does not affect the result. These
consumers pin something stronger: a definition with **no record argument at all**
that is the record-taking read, by `rfl`. A controller can call it.
-/

/--
Pins the record-free read's signature: a segment layout, a supplied store and an
index. No table, no shape, no list, no proof argument.
-/
def packedSelectEntryReadSignature :
    GenericSelect.SparseDenseEntryTableTraceSegmentBases ->
      WordRAM.ReadStore -> Nat ->
        WordRAM.TraceResult
          (Option GenericSelect.SparseDenseSelectDenseLocalEntry) :=
  packedSelectEntryRead

/-- Pins that the record-free read is the record-taking read, at every table. -/
theorem packedSelectEntryReadIsTheLeafRead :
    forall {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
      {fieldWidth : Nat}
      (table :
        GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
          entries fieldWidth)
      (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
      (store : WordRAM.ReadStore) (index : Nat),
      table.readTraceResultRelabeledWithStore layout store index =
        packedSelectEntryRead layout store index :=
  fun table layout store index =>
    packedSelectEntryRead_eq table layout store index

/--
Pins the record-free rank read's signature: segments, a target bit, a supplied
store, and the three scalars. No record, no shape, no proof argument.
-/
def packedRankReadSignature :
    Nat -> Nat -> Nat -> Nat -> Nat -> Bool -> WordRAM.ReadStore ->
      Nat -> Nat -> Nat -> Nat -> WordRAM.TraceResult Nat :=
  packedRankRead

/-- Pins that the record-free rank read is the record-taking one. -/
theorem packedRankReadIsTheLeafRankRead :
    forall {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
      (data :
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
          bits superOverhead blockOverhead queryCost)
      (store : WordRAM.ReadStore)
      (superSegment blockSegment wordSegment chunkSegment chunkBits : Nat)
      (target : Bool) (pos : Nat),
      data.bpChunkedRankTraceResultWithStore store superSegment blockSegment
          wordSegment chunkSegment chunkBits target pos =
        packedRankRead superSegment blockSegment wordSegment chunkSegment
          chunkBits target store bits.length data.wordSize data.blocksPerSuper
          pos :=
  fun data store superSegment blockSegment wordSegment chunkSegment chunkBits
      target pos =>
    packedRankRead_eq data store superSegment blockSegment wordSegment
      chunkSegment chunkBits target pos

/-- Pins the record-free sparse-directory read's signature. -/
def packedSparseDirectoryReadSignature :
    GenericSelect.SparseExceptionDirectoryTraceSegmentBases ->
      Nat -> WordRAM.ReadStore -> Nat ->
        Nat -> Nat -> Nat -> Nat ->
          Nat -> Nat -> Nat -> WordRAM.TraceResult (Option Nat) :=
  packedSparseDirectoryRead

/-- Pins that the record-free sparse-directory read is the record-taking one. -/
theorem packedSparseDirectoryReadIsTheLeafDirectoryRead :
    forall {bits : List Bool} {target : Bool}
      {rankSuperOverhead rankBlockOverhead : Nat}
      (directory :
        GenericSelect.SparseExceptionDirectory
          bits target rankSuperOverhead rankBlockOverhead)
      (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
      (chunkSegment : Nat) (store : WordRAM.ReadStore) (chunkBits : Nat)
      (base localSlot localOccurrence : Nat),
      directory.bpChunkedReadTraceResultWithStore layout chunkSegment store
          chunkBits base localSlot localOccurrence =
        packedSparseDirectoryRead layout chunkSegment store chunkBits
          directory.flagBits.length directory.rankData.wordSize
          directory.rankData.blocksPerSuper directory.localStride base localSlot
          localOccurrence :=
  fun directory layout chunkSegment store chunkBits base localSlot
      localOccurrence =>
    packedSparseDirectoryRead_eq directory layout chunkSegment store chunkBits
      base localSlot localOccurrence

/-! #### The whole select leaf is record-free

The consumers below pin the leaf itself, not just its helpers. The signature
carries the `FG-07` claim for this component: segments, a supplied store,
geometry scalars, the target bit and the query index — no
`SparseExceptionSelectData`, no `CartesianShape`, no list, no proof argument.
-/

/-- Pins the record-free leaf's signature. -/
def packedSelectCloseReadSignature :
    GenericSelect.SparseExceptionSelectTraceSegmentLayout ->
      Nat -> Nat -> WordRAM.ReadStore -> Nat -> Bool ->
        Nat -> Nat -> Nat -> Nat -> Nat ->
          Nat -> Nat -> Nat ->
            Nat -> Nat -> Nat -> Nat ->
              Nat -> WordRAM.TraceResult (Option Nat) :=
  packedSelectCloseRead

/--
Pins that the record-free leaf is the leaf, at every `SparseExceptionSelectData`
and every store.
-/
theorem packedSelectCloseReadIsTheLeaf :
    forall {bits : List Bool} {target : Bool}
      {rankSuperOverhead rankBlockOverhead : Nat}
      (data :
        GenericSelect.SparseExceptionSelectData
          bits target rankSuperOverhead rankBlockOverhead)
      (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
      (chunkSegment selectTableSegment : Nat) (store : WordRAM.ReadStore)
      (chunkBits idx : Nat),
      data.bpChunkedSelectTraceResultWithStore layout chunkSegment
          selectTableSegment store chunkBits idx =
        packedSelectCloseRead layout chunkSegment selectTableSegment store
          chunkBits target (GenericSelect.occurrenceCount bits target)
          data.superStride data.wordSize data.localSlotsPerSuper
          data.localStride data.longFlagBits.length
          data.longFlagRankData.wordSize data.longFlagRankData.blocksPerSuper
          data.sparseDirectory.flagBits.length
          data.sparseDirectory.rankData.wordSize
          data.sparseDirectory.rankData.blocksPerSuper
          data.sparseDirectory.localStride idx :=
  fun data layout chunkSegment selectTableSegment store chunkBits idx =>
    packedSelectCloseRead_eq data layout chunkSegment selectTableSegment store
      chunkBits idx

/-- Pins the record-free close-side rank leaf's signature. -/
def packedRankCloseReadSignature :
    WordRAM.ReadStore -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat ->
      WordRAM.TraceResult Nat :=
  packedRankCloseRead

/--
Pins that the whole-query program's `rankCloseIfSome` leaf is the record-free
rank read. Two of the four instruction leaves are now record-free; the third,
`outputPredIfSome`, touches no store at all.
-/
theorem packedRankCloseReadIsTheCloseRankLeaf :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (rankSegmentBase pos : Nat),
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
          rankSegmentBase pos =
        packedRankCloseRead store rankSegmentBase
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          shape.bpCode.length
          (builtRelativeSplitBPCloseRankData shape).wordSize
          (builtRelativeSplitBPCloseRankData shape).blocksPerSuper pos :=
  packedRankCloseRead_eq

/-! #### Where the shape still enters

`lcaClose` is the one whole-query instruction whose leaf takes a
`CartesianShape` directly rather than a derived record. The first consumer pins
that — it is the surface a controller cannot call as it stands. The second
discharges the rank seed that leaf supplies, leaving the shape argument as the
sole residue.
-/

/-- Pins that the close/LCA leaf still takes a shape. -/
def packedLcaCloseLeafSignaturePin :
    CartesianShape -> WordRAM.ReadStore -> Nat -> Nat ->
      WordRAM.TraceResult (Option Nat) :=
  packedLcaCloseLeafSignature

/-- Pins the close dispatch block size as a function of the input size. -/
def packedSummaryBlockSizeRawSignature : Nat -> Nat :=
  packedSummaryBlockSizeRaw

/--
Pins that the close/LCA navigator's same-block versus cross-block dispatch is
decided by `n` and the two close endpoints alone. The block size is
`2 * (n.log2 + 1)`.
-/
theorem packedCloseDispatchIsSizeOnly :
    forall shape : CartesianShape,
      SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape =
        packedSummaryBlockSizeRaw shape.size :=
  packedSummaryBlockSizeRaw_eq

/-- Pins the size-only local-BP window base. -/
def packedLocalBPWindowBaseSignature : Nat -> Nat -> Nat -> Nat :=
  packedLocalBPWindowBase

/--
Pins that the same-block sub-navigator's local-BP seed is shape-free: its only
shape use was the window base, and that is a function of the input size.
-/
theorem packedLocalBPSeedIsShapeFree :
    forall (shape : CartesianShape)
      (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
      (blockSize close : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize close =
        packedLocalBPSeed shape.size rankCloseTrace blockSize close :=
  packedLocalBPSeed_eq

/--
Pins that the same-block seeded reader is shape-free given its window trace. Its
fringe chunk width and window base come from the input size; the window reader is
now an argument.
-/
theorem packedSameBlockCloseSeededReadIsShapeFree :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (fringeSegment blockSize leftClose rightClose seed : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
          shape store fringeSegment blockSize leftClose rightClose seed =
        packedSameBlockCloseSeededRead store fringeSegment
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
            shape store blockSize leftClose)
          shape.size blockSize leftClose rightClose seed :=
  packedSameBlockCloseSeededRead_eq

/-- Pins that the rank seed it supplies is already record-free. -/
theorem packedLcaCloseRankSeedIsRecordFree :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore) (pos : Nat),
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
          concreteBPNativeRankCloseTraceSegmentBase pos =
        packedRankCloseRead store concreteBPNativeRankCloseTraceSegmentBase
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          shape.bpCode.length
          (builtRelativeSplitBPCloseRankData shape).wordSize
          (builtRelativeSplitBPCloseRankData shape).blocksPerSuper pos :=
  packedLcaCloseRankSeed_eq

/-- Pins the record-free dense two-word select read's signature. -/
def packedDenseTwoWordSelectReadSignature :
    Nat -> Nat -> Nat -> Nat -> Bool -> WordRAM.ReadStore -> Nat ->
      Nat -> Nat -> Nat -> WordRAM.TraceResult (Option Nat) :=
  packedDenseTwoWordSelectRead

/-- Pins the fringe chunk width mirror's signature. -/
def packedFringeChunkBitsSignature : Nat -> Nat := packedFringeChunkBits

/--
Pins the one scalar supplied beside the select data: the fringe chunk width the
leaf receives as `c`. It is a function of the input size.
-/
theorem packedFringeChunkBitsIsSizeOnly :
    forall shape : CartesianShape,
      SuccinctClose.bpFringeChunkBits shape.bpCode.length =
        packedFringeChunkBits shape.size :=
  packedFringeChunkBits_eq

/--
Pins that both rank records the select leaf uses group one block per super
block. These are the last two select-side scalars; both are literals, so neither
needs a mirror and neither can carry shape content.
-/
theorem packedLongFlagBlocksPerSuperIsOne :
    forall (bits : List Bool) (target : Bool),
      (GenericSelect.longFlagRankData bits target).blocksPerSuper = 1 :=
  packedLongFlagBlocksPerSuper_eq

theorem packedSparseFlagBlocksPerSuperIsOne :
    forall (bits : List Bool) (target : Bool),
      (GenericSelect.sparseExceptionEffectiveFlagRankData
          bits target).blocksPerSuper = 1 :=
  packedSparseFlagBlocksPerSuper_eq

/-- Pins the clamped query position as a function of the bit length and position. -/
def packedRankQueryPosSignature : Nat -> Nat -> Nat := packedRankQueryPos

/--
Pins that a rank read's query position is a function of the bit length alone, so
one of its three scalars is already reduced to a length this development mirrors.
-/
theorem packedRankQueryPosIsTheBitLengthAlone :
    forall {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
      (data :
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
          bits superOverhead blockOverhead queryCost)
      (pos : Nat),
      data.queryPos pos = packedRankQueryPos bits.length pos :=
  fun data pos => packedRankQueryPos_eq data pos

/--
Pins the sparse-directory read is determined by four scalars, over
directories with unrelated bit strings, targets and overheads.
-/
theorem packedSparseDirectoryReadIsDeterminedByFourScalars :
    forall {bitsLeft bitsRight : List Bool} {targetLeft targetRight : Bool}
      {superLeft blockLeft superRight blockRight : Nat}
      (directoryLeft :
        GenericSelect.SparseExceptionDirectory
          bitsLeft targetLeft superLeft blockLeft)
      (directoryRight :
        GenericSelect.SparseExceptionDirectory
          bitsRight targetRight superRight blockRight)
      (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
      (chunkSegment : Nat) (store : WordRAM.ReadStore) (chunkBits : Nat)
      (base localSlot localOccurrence : Nat),
      directoryLeft.rankData.queryPos localSlot =
          directoryRight.rankData.queryPos localSlot ->
        directoryLeft.rankData.wordSize = directoryRight.rankData.wordSize ->
          directoryLeft.rankData.blocksPerSuper =
              directoryRight.rankData.blocksPerSuper ->
            directoryLeft.localStride = directoryRight.localStride ->
              directoryLeft.bpChunkedReadTraceResultWithStore layout
                  chunkSegment store chunkBits base localSlot localOccurrence =
                directoryRight.bpChunkedReadTraceResultWithStore layout
                  chunkSegment store chunkBits base localSlot localOccurrence :=
  fun directoryLeft directoryRight layout chunkSegment store chunkBits base
      localSlot localOccurrence hquery hwordSize hblocks hlocalStride =>
    packedSparseDirectoryRead_scalar_determined directoryLeft directoryRight
      layout chunkSegment store chunkBits base localSlot localOccurrence hquery
      hwordSize hblocks hlocalStride

/-- Pins that the relative-offset read takes a store and three naturals only. -/
def packedRelativeOffsetReadSignaturePin :
    WordRAM.ReadStore -> Nat -> Nat -> Nat ->
      WordRAM.TraceResult (Option Nat) :=
  packedRelativeOffsetReadSignature

/-! #### The long count is obtained by a probe

Every packed address takes the decoded long count as an argument. These consumers
pin where a controller gets it: one physical probe of cell zero.
-/

/-- Pins that the header probe costs exactly one probe. -/
theorem packedHeaderProbeCostsOneProbe : packedHeaderProbePlan.length = 1 :=
  packedHeaderProbePlan_length

/-- Pins that the header probe is allocated and returns the header cell. -/
theorem packedHeaderProbeFetchesTheHeaderCell :
    forall shape : CartesianShape,
      packedFetch (packedMemory shape) packedHeaderProbePlan =
        some [packedHeaderBits shape] :=
  packedHeaderFetch

/--
Pins that decoding the header probe yields exactly the long count, at every size
and with no side condition. Without this the long count would be a shape field
supplied from outside, which is what `FG-07` forbids.
-/
theorem packedLongCountComesFromAProbe :
    forall shape : CartesianShape,
      (packedFetch (packedMemory shape) packedHeaderProbePlan).map
          (fun cells => SuccinctSpace.bitsToNatLE cells.flatten) =
        some (longCount shape) :=
  packedHeaderProbe_decode

/-! #### The BP code lowers completely

The BP code is the first source whose logical read is lowered with **both** a
shape-free address and a shape-free width. It is also the case that forced the
stride and the read width apart: the code is chunked into
`machineWordBits (2n)`-bit words and the final word is short whenever `2n` is not
a multiple of that width, so reading it at full width would pull bits belonging
to the next component.
-/

/-- Pins the strided address signature: the stride is separate from the width. -/
def packedStridedBitAddressSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource ->
      Nat -> Nat -> Nat :=
  packedStridedBitAddress

/-- Pins the BP-code stride as a function of the input size alone. -/
def packedBpCodeWordWidthSignature : Nat -> Nat := packedBpCodeWordWidth

/-- Pins the BP-code read width as a function of the input size and index. -/
def packedBpCodeReadWidthSignature : Nat -> Nat -> Nat := packedBpCodeReadWidth

/-- Pins that a BP-code word fits one packed cell. -/
theorem packedBpCodeWordFitsOneCell :
    forall n : Nat, packedBpCodeWordWidth n <= packedCellWidth n :=
  packedBpCodeWordWidth_le_cellWidth

/-- Pins that the BP code starts the canonical payload. -/
theorem packedBpCodeStartsThePayload :
    forall n longCount : Nat,
      packedSourceFlatOffset n longCount
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode = 0 :=
  packedBpCode_flatOffset

/--
Pins the complete lowering: every BP-code word the flat payload store would
return is fetched and decoded by the physical probe plan at the strided address
and the exact read width, both computed from the input size and the index alone.
-/
theorem packedBpCodeReadDecodesToTheStoreWord :
    forall (shape : CartesianShape) (index : Nat) (word : List Bool),
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode)[index]? =
          some word ->
        (packedFetch (packedMemory shape)
              (packedProbePlan shape.size
                (packedStridedBitAddress shape.size (longCount shape)
                  ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode index
                  (packedBpCodeWordWidth shape.size))
                (packedBpCodeReadWidth shape.size index))).map
            (packedDecodeSpan shape.size
              (packedStridedBitAddress shape.size (longCount shape)
                ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode index
                (packedBpCodeWordWidth shape.size))
              (packedBpCodeReadWidth shape.size index)) =
          some word :=
  fun shape _ _ hget => packedBpCodeRead_decode shape hget

/-! #### The two boundary facts that make the repair real -/

/--
Pins that the address one past the last allocated cell is absent. The
unconditional plan issued exactly this address for a read inside the final cell;
only the total cell accessor made that look harmless.
-/
theorem packedOnePastLastCellIsAbsent :
    forall shape : CartesianShape,
      (packedMemory shape)[packedCellCount shape.size]? = none :=
  packedMemory_getElem?_cellCount

/--
Pins the final-allocated-cell boundary case: a read contained in the last cell
issues exactly one probe, that probe is the last cell, and the fetch succeeds.
-/
theorem packedFinalCellReadIssuesOneAllocatedProbe :
    forall (shape : CartesianShape) (offset width : Nat),
      0 < width ->
        offset + width <= packedCellWidth shape.size ->
          packedProbePlan shape.size
              (offset +
                (packedCellCount shape.size - 1) * packedCellWidth shape.size)
              width =
            [packedCellCount shape.size - 1] /\
          packedFetch (packedMemory shape)
              (packedProbePlan shape.size
                (offset +
                  (packedCellCount shape.size - 1) *
                    packedCellWidth shape.size)
                width) =
            some [packedCellAt shape (packedCellCount shape.size - 1)] :=
  fun shape _ _ hpos hin => packedProbe_final_cell shape hpos hin

/-- Pins that a genuinely crossing read still issues both cells. -/
theorem packedCrossingReadIssuesTwoProbes :
    forall n base offset width : Nat,
      offset < packedCellWidth n ->
        packedCellWidth n < offset + width ->
          packedProbePlan n (offset + base * packedCellWidth n) width =
            [base, base + 1] :=
  packedProbePlan_of_crossing

/-! #### Concrete boundary instances

The general theorems above are instantiated at the smallest shapes so that the
conditional plan is exercised, not merely stated. Each instance is
kernel-checked; none uses a native decision procedure.
-/

/--
A one-bit read at the start of the final allocated cell, empty shape.

The sizes are written as `shape.size` rather than as numerals so that the
instance is checked without asking the elaborator to evaluate the payload-length
arithmetic; the corresponding numeral facts are pinned separately above by
`packedSizeTwoLeftHasSizeTwo` and its neighbours.
-/
theorem packedEmptyShapeFinalCellRead :
    packedProbePlan CartesianShape.empty.size
        (0 + (packedCellCount CartesianShape.empty.size - 1) *
          packedCellWidth CartesianShape.empty.size) 1 =
      [packedCellCount CartesianShape.empty.size - 1] /\
    packedFetch (packedMemory CartesianShape.empty)
        (packedProbePlan CartesianShape.empty.size
          (0 + (packedCellCount CartesianShape.empty.size - 1) *
            packedCellWidth CartesianShape.empty.size) 1) =
      some
        [packedCellAt CartesianShape.empty
          (packedCellCount CartesianShape.empty.size - 1)] :=
  packedProbe_final_cell CartesianShape.empty (by omega)
    (by have := packedCellWidth_pos CartesianShape.empty.size; omega)

/-- The same boundary read on the singleton shape. -/
theorem packedSingletonFinalCellRead :
    packedProbePlan
        (CartesianShape.node CartesianShape.empty CartesianShape.empty).size
        (0 +
          (packedCellCount
              (CartesianShape.node CartesianShape.empty
                CartesianShape.empty).size - 1) *
            packedCellWidth
              (CartesianShape.node CartesianShape.empty
                CartesianShape.empty).size) 1 =
      [packedCellCount
          (CartesianShape.node CartesianShape.empty
            CartesianShape.empty).size - 1] /\
    packedFetch
        (packedMemory
          (CartesianShape.node CartesianShape.empty CartesianShape.empty))
        (packedProbePlan
          (CartesianShape.node CartesianShape.empty CartesianShape.empty).size
          (0 +
            (packedCellCount
                (CartesianShape.node CartesianShape.empty
                  CartesianShape.empty).size - 1) *
              packedCellWidth
                (CartesianShape.node CartesianShape.empty
                  CartesianShape.empty).size) 1) =
      some
        [packedCellAt
          (CartesianShape.node CartesianShape.empty CartesianShape.empty)
          (packedCellCount
            (CartesianShape.node CartesianShape.empty
              CartesianShape.empty).size - 1)] :=
  packedProbe_final_cell
    (CartesianShape.node CartesianShape.empty CartesianShape.empty) (by omega)
    (by
      have :=
        packedCellWidth_pos
          (CartesianShape.node CartesianShape.empty CartesianShape.empty).size
      omega)

/-- The same boundary read on the left-leaning shape of size two. -/
theorem packedSizeTwoLeftFinalCellRead :
    packedProbePlan packedSizeTwoLeft.size
        (0 + (packedCellCount packedSizeTwoLeft.size - 1) *
          packedCellWidth packedSizeTwoLeft.size) 1 =
      [packedCellCount packedSizeTwoLeft.size - 1] /\
    packedFetch (packedMemory packedSizeTwoLeft)
        (packedProbePlan packedSizeTwoLeft.size
          (0 + (packedCellCount packedSizeTwoLeft.size - 1) *
            packedCellWidth packedSizeTwoLeft.size) 1) =
      some
        [packedCellAt packedSizeTwoLeft
          (packedCellCount packedSizeTwoLeft.size - 1)] :=
  packedProbe_final_cell packedSizeTwoLeft (by omega)
    (by have := packedCellWidth_pos packedSizeTwoLeft.size; omega)

/-- The same boundary read on the right-leaning shape of size two. -/
theorem packedSizeTwoRightFinalCellRead :
    packedProbePlan packedSizeTwoRight.size
        (0 + (packedCellCount packedSizeTwoRight.size - 1) *
          packedCellWidth packedSizeTwoRight.size) 1 =
      [packedCellCount packedSizeTwoRight.size - 1] /\
    packedFetch (packedMemory packedSizeTwoRight)
        (packedProbePlan packedSizeTwoRight.size
          (0 + (packedCellCount packedSizeTwoRight.size - 1) *
            packedCellWidth packedSizeTwoRight.size) 1) =
      some
        [packedCellAt packedSizeTwoRight
          (packedCellCount packedSizeTwoRight.size - 1)] :=
  packedProbe_final_cell packedSizeTwoRight (by omega)
    (by have := packedCellWidth_pos packedSizeTwoRight.size; omega)

/--
A two-bit read starting at the last bit of cell zero really does cross, at the
empty shape. Together with the instances above this shows both branches of the
conditional are reachable at the smallest sizes.
-/
theorem packedEmptyShapeCrossingRead :
    packedProbePlan 0 (packedCellWidth 0 - 1 + 0 * packedCellWidth 0) 2 =
      [0, 1] :=
  packedProbePlan_of_crossing 0 0 (packedCellWidth 0 - 1) 2
    (by have := packedCellWidth_pos 0; omega)
    (by have := packedCellWidth_ge_two 0; omega)

/-- The same crossing read at the singleton shape's size. -/
theorem packedSingletonCrossingRead :
    packedProbePlan 1 (packedCellWidth 1 - 1 + 0 * packedCellWidth 1) 2 =
      [0, 1] :=
  packedProbePlan_of_crossing 1 0 (packedCellWidth 1 - 1) 2
    (by have := packedCellWidth_pos 1; omega)
    (by have := packedCellWidth_ge_two 1; omega)

/-- The same crossing read at size two. -/
theorem packedSizeTwoCrossingRead :
    packedProbePlan 2 (packedCellWidth 2 - 1 + 0 * packedCellWidth 2) 2 =
      [0, 1] :=
  packedProbePlan_of_crossing 2 0 (packedCellWidth 2 - 1) 2
    (by have := packedCellWidth_pos 2; omega)
    (by have := packedCellWidth_ge_two 2; omega)

end Validation
end PackedCellProbe
end SuccinctFinal
end RMQ

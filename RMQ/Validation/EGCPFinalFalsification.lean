import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceFactorization
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Payload
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Header
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Space
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Address
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceWords
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceGeometry
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.WordWidth
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.PhysicalRead
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Boundaries
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerPayload
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerProof
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerStateProof
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCapstone

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

The proof-free first-order controller, the ordered whole-run lowering, the
same-run reference correctness, and the locally owned seven-case `R2-ALLSIZE`
replay stage all exist and are pinned by the consumers below. The Stage-F
residual campaign's combined capstone (`FG-13`), the universal header-liveness
theorem, the pinned decisive-cell and unread-cell fixture theorems (`FG-11`),
and the boundary instances (`FG-14`) are pinned in the closing sections of
this file; the sixteen-case `FG-12` replay is owned by
`scripts/eg_cp_final_falsification_replay.ps1`, and coordinator
`FEASIBILITY_PASS` remains a separate open decision.
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

/-! #### The whole close/LCA route is shape-free

`DD-20260804-011` recorded `lcaClose` as the one instruction whose leaf took a
`CartesianShape` directly. That residue is now discharged: the dispatcher, both
branches, and every callee beneath them have shape-free mirrors.
-/

/-- Pins the shape-free close/LCA route's signature. -/
def packedLcaCloseReadSignature :
    (Nat -> WordRAM.TraceResult Nat) ->
      SuccinctClose.BPRelativeRmmInteriorTraceSegments ->
        Nat -> WordRAM.ReadStore -> Nat -> Nat -> Nat ->
          WordRAM.TraceResult (Option Nat) :=
  packedLcaCloseRead

/--
Pins that every read the `lcaClose` instruction issues is expressible from the
input size, the supplied store, the fixed segment constants, the caller's rank
reader and the two close endpoints.
-/
theorem packedLcaCloseRouteIsShapeFree :
    forall (shape : CartesianShape)
      (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
      (segments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
      (fringeSegment : Nat) (store : WordRAM.ReadStore)
      (sameBlockSegment leftClose rightClose : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
          shape rankCloseTrace segments fringeSegment store sameBlockSegment
          leftClose rightClose =
        packedLcaCloseRead rankCloseTrace segments fringeSegment store
          shape.size leftClose rightClose :=
  packedLcaCloseRead_eq

/-- Pins that the cross-block branch is shape-free. -/
theorem packedCrossBlockCloseBranchIsShapeFree :
    forall (shape : CartesianShape)
      (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
      (segments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
      (fringeSegment : Nat) (store : WordRAM.ReadStore)
      (leftClose rightClose : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
          shape rankCloseTrace segments fringeSegment store leftClose
          rightClose =
        packedCrossBlockCloseRead rankCloseTrace segments fringeSegment store
          shape.size leftClose rightClose :=
  packedCrossBlockCloseRead_eq

/-! #### The controller

`FG-07` asks for one fixed definition whose dynamic inputs are exactly `n`, the
query endpoints, the header reply and previous replies from the packed memory,
with no `CartesianShape`, source program, list, proof callback or expected
answer.

The signature below is written out independently of the definition, so restoring
a `shape` parameter, adding a program argument, or threading a proof callback
breaks this ascription rather than being absorbed by it.
-/

/--
Pins the controller's exact type: a supplied store and three naturals. No
`CartesianShape`, no `WholeQueryProgram` argument, no `List Int`, no proof
argument, no expected answer.
-/
def packedWholeQueryRunSignature :
    WordRAM.ReadStore -> Nat -> Nat -> Nat ->
      WordRAM.TraceResult (Option Nat) :=
  packedWholeQueryRun

/--
Pins that the controller **is** the existing supplied-store whole-query
execution, at every shape, store and endpoint pair. The equation is between the
`TraceResult`s themselves, so value, modeled cost and ordered trace all agree.
-/
theorem packedControllerIsTheWholeQueryRun :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (left right : Nat),
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore shape
          store left right =
        packedWholeQueryRun store shape.size left right :=
  packedWholeQueryRun_eq

/-- Pins that one instruction step is shape-free. -/
theorem packedInstrStepIsShapeFree :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (left right : Nat) (instr : WholeQueryInstr) (state : WholeQueryState),
      instr.evalGlobalWordTraceWithStore shape store left right state =
        packedInstrStep store shape.size left right instr state :=
  packedInstrStep_eq

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

/--
Pins that the close-side rank leaf is a function of the input size alone: every
argument is `n`, the supplied store, the segment base or the position. This is
the strongest form for that leaf -- no shape-derived quantity survives.
-/
theorem packedRankCloseReadIsSizeOnly :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (rankSegmentBase pos : Nat),
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
          rankSegmentBase pos =
        packedRankCloseRead store rankSegmentBase
          (packedFringeChunkBits shape.size) (2 * shape.size)
          (packedBpCodeWordWidth shape.size) (packedBpCodeWordWidth shape.size)
          pos :=
  packedRankCloseRead_size_only

/-- Pins the interior layout mirror's signature. -/
def packedInteriorLayoutSignature : Nat -> SuccinctClose.RelativeRmm.Layout :=
  packedInteriorLayout

/--
Pins that the interior navigator's control-flow record is a function of the
input size. Every field of `RelativeRmm.canonicalLayout shape` is a summary
scalar already mirrored.
-/
theorem packedInteriorLayoutIsSizeOnly :
    forall shape : CartesianShape,
      SuccinctClose.RelativeRmm.canonicalLayout shape =
        packedInteriorLayout shape.size :=
  packedInteriorLayout_eq

/--
Pins the interior read's table-free signature: input size, entry count, width,
base, index. Five naturals -- no table, no shape, no proof argument.
-/
def packedInteriorReadNatOfSignature : Nat -> Nat -> Nat -> Nat -> Nat ->
    SuccinctSpace.FlatStoreComputation (Option Nat) :=
  packedInteriorReadNatOf

/--
Pins that the canonical interior read *is* that five-natural function, at every
shape and every fixed-width table.
-/
theorem packedInteriorReadIsFiveNaturals :
    forall {entries : List Nat} {width : Nat} (shape : CartesianShape)
      (table : SuccinctSpace.FixedWidthNatTable entries width) (base i : Nat),
      SuccinctClose.canonicalRelativeRmmMachineReadNatComputation shape table
          base i =
        packedInteriorReadNatOf shape.size entries.length width base i :=
  fun shape table base i => packedInteriorReadNatOf_eq shape table base i

/-! #### The interior computation tower is shape-free

All ten interior `FlatStoreComputation` definitions now have shape-free mirrors,
from the summary read at the bottom to the range-min dispatcher at the top.
-/

/-- Pins the top interior computation's signature: three naturals. -/
def packedInteriorRangeMinComputationSignature :
    Nat -> Nat -> Nat ->
      SuccinctSpace.FlatStoreComputation (Option (Prod Nat Nat)) :=
  packedInteriorRangeMinComputation

/--
Pins that the interior range-min computation -- the top of the interior tower --
is a function of the input size and the two block arguments.
-/
theorem packedInteriorRangeMinComputationIsSizeOnly :
    forall (shape : CartesianShape) (startBlock count : Nat),
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation shape
          startBlock count =
        packedInteriorRangeMinComputation shape.size startBlock count :=
  packedInteriorRangeMinComputation_eq

/-- Pins the interior offsets mirror's signature. -/
def packedInteriorOffsetsSignature :
    Nat -> SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets :=
  packedInteriorOffsets

/--
Pins that the nine interior component offsets are functions of the input size.

`GeometryClosure.offsets_congr` says two shapes of equal size agree on all nine;
this says what they *are*, so a controller can compute the interior's addresses
from `n`. With `packedInteriorLayoutIsSizeOnly` this is both halves of the
interior's shape dependence: control flow and addresses.
-/
theorem packedInteriorOffsetsAreSizeOnly :
    forall shape : CartesianShape,
      SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets shape =
        packedInteriorOffsets shape.size :=
  packedInteriorOffsets_eq

/-- Pins the interior component store's word count as size-only. -/
theorem packedInteriorComponentWordsAreSizeOnly :
    forall shape : CartesianShape,
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words.size =
        packedInteriorComponentWords shape.size :=
  packedInteriorComponentWords_eq

/-! #### The endpoint-fringe candidate readers are shape-free

The cross-block branch's two endpoint readers needed no new mirrors: their only
shape-derived inputs are the fringe chunk width, the local-BP window base and the
window reader, all already handled.
-/

theorem packedLeftFringeCandidateReadIsShapeFree :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (fringeSegment blockSize leftClose seed : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
          shape store fringeSegment blockSize leftClose seed =
        packedLeftFringeCandidateRead store fringeSegment shape.size blockSize
          leftClose seed :=
  packedLeftFringeCandidateRead_eq

theorem packedRightFringeCandidateReadIsShapeFree :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (fringeSegment blockSize rightClose seed : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
          shape store fringeSegment blockSize rightClose seed =
        packedRightFringeCandidateRead store fringeSegment shape.size blockSize
          rightClose seed :=
  packedRightFringeCandidateRead_eq

/-! #### The same-block close branch is shape-free

Composing the seed, the window reader and the seeded reader. The rank-close
reader remains a supplied argument, and `packedRankCloseReadIsSizeOnly` shows the
caller can build it from `n`.
-/

/-- Pins the shape-free same-block branch's signature. -/
def packedSameBlockCloseDecodedReadSignature :
    WordRAM.ReadStore -> (Nat -> WordRAM.TraceResult Nat) ->
      Nat -> Nat -> Nat -> Nat -> Nat -> WordRAM.TraceResult (Option Nat) :=
  packedSameBlockCloseDecodedRead

/--
Pins that the whole same-block close branch is shape-free: every shape use in it
-- the seed's window base, the seeded reader's fringe width and window base, and
the window reader's word size -- is a function of the input size.
-/
theorem packedSameBlockCloseBranchIsShapeFree :
    forall (shape : CartesianShape)
      (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
      (fringeSegment : Nat) (store : WordRAM.ReadStore)
      (blockSize leftClose rightClose : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape rankCloseTrace fringeSegment store blockSize leftClose
          rightClose =
        packedSameBlockCloseDecodedRead store rankCloseTrace fringeSegment
          shape.size blockSize leftClose rightClose :=
  packedSameBlockCloseDecodedRead_eq

/-- Pins that the local window reader is shape-free. -/
theorem packedLocalBPWindowBitsReadIsShapeFree :
    forall (shape : CartesianShape) (store : WordRAM.ReadStore)
      (blockSize close : Nat),
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
          shape store blockSize close =
        packedLocalBPWindowBitsRead store shape.size blockSize close :=
  packedLocalBPWindowBitsRead_eq

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

/-! ## The physical read (`FG-08`, `INV-WORD-WIDTH`)

The signatures below are written out here, so restoring a `CartesianShape`
argument to the read, or widening a stored word past one cell, breaks this file.
-/

/--
The physical read's exact type: a size, a decoded long count, a packed memory, a
typed source and an index. No `CartesianShape`, no store, no proof callback.
-/
def packedSourceReadSignature :
    Nat -> Nat -> List (List Bool) ->
      ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat -> Option (List Bool) :=
  packedSourceRead

/-- The probe plan's exact type, likewise shape-free. -/
def packedSourceReadPlanSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat ->
      List Nat :=
  packedSourceReadPlan

/-- Every stored word fits one packed cell, under the controller's own guard. -/
theorem packedEveryStoredWordFitsOneCell :
    forall (n : Nat) (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
      PackedSourceCounted n source ->
        packedSourceStride n source <= packedCellWidth n :=
  packedSourceStride_le_cellWidth

/-- A logical word read is charged at most two physical probes. -/
theorem packedLogicalWordReadIsAtMostTwoProbes :
    forall (n longCount : Nat)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat),
      (packedSourceReadPlan n longCount source index).length <= 2 :=
  packedSourceReadPlan_length_le_two

/--
**Every successful logical word read lowers.** The flat payload store's answer is
reproduced exactly by probing the packed memory.
-/
theorem packedEverySuccessfulReadLowers :
    forall (shape : Cartesian.CartesianShape)
      (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
      {index : Nat} {word : List Bool},
      PackedSourceCounted shape.size source ->
        (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source)[index]? =
            some word ->
          packedSourceRead shape.size (longCount shape) (packedMemory shape)
              source index =
            some word :=
  packedSourceRead_of_some

/--
The word geometry is a function of the input size and the decoded long count
alone. Restoring a shape argument to any of the three breaks these ascriptions.
-/
def packedSourceStrideSignature :
    Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  packedSourceStride

def packedSourceWordCountSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  packedSourceWordCount

def packedSourceBitLengthSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  packedSourceBitLength

/--
The one source whose word count is not size-only, recorded as an inequality so
that the asymmetry is visible in the consumer rather than only in the library.
-/
theorem packedSparseRelativeIsBoundedNotDetermined :
    forall shape : Cartesian.CartesianShape,
      (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length <=
        packedSparseRelativeCapacity shape.size :=
  packedSparseRelativeEntries_le_capacity

/-! ## The packed memory as a read store (`FG-08`) -/

/-- The store's exact type: a size, a decoded long count and a packed memory. -/
def packedBackedStoreSignature :
    Nat -> Nat -> List (List Bool) -> WordRAM.ReadStore :=
  packedBackedStore

/-- Every successful store read is answered identically by probing. -/
theorem packedBackedStoreAnswersEverySuccessfulRead :
    forall (shape : Cartesian.CartesianShape) {segment index : Nat}
      {word : List Bool},
      (segment = 24 ->
        SuccinctClose.concreteBPRelativeRmmInteriorReady shape) ->
      (segment = 25 ->
        SuccinctClose.concreteBPRelativeRmmInteriorReady shape) ->
      (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? segment
          index = some word ->
        (packedBackedStore shape.size (longCount shape)
            (packedMemory shape)).readWord? segment index = some word :=
  packedBackedStore_of_some

/--
Away from the one source whose word count is not size-only, and under the
readiness guard, the two stores are equal at that address -- failures included.
-/
theorem packedBackedStoreAgreesAwayFromTheSparseTable :
    forall (shape : Cartesian.CartesianShape) {segment index : Nat},
      (packedSegmentSource? segment !=
        some ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative) ->
      (segment = 24 ->
        SuccinctClose.concreteBPRelativeRmmInteriorReady shape) ->
      (segment = 25 ->
        SuccinctClose.concreteBPRelativeRmmInteriorReady shape) ->
        (packedBackedStore shape.size (longCount shape)
            (packedMemory shape)).readWord? segment index =
          (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
            segment index :=
  packedBackedStore_eq_readWord

/-! ## Addresses fit the modeled machine word (`INV-ADDRESS-WIDTH`) -/

/--
Every issued probe address is representable in one modeled machine word, not
merely below the host array's length -- which is the substitution the row
rejects.
-/
theorem packedIssuedAddressesAreMachineRepresentable :
    forall {n bit width addr : Nat},
      bit + width <= packedAllocatedBits n ->
        addr ∈ packedProbePlan n bit width ->
          addr < 2 ^ packedCellWidth n :=
  packedProbeAddress_lt_two_pow_cellWidth

/-- The allocated-cell count itself fits the modeled word. -/
theorem packedCellCountIsMachineRepresentable :
    forall n : Nat, packedCellCount n < 2 ^ packedCellWidth n :=
  packedCellCount_lt_two_pow_cellWidth

/-! ## Named geometry thresholds (`FG-14`) -/

/--
The long crossover, minus one / at / plus one. The threshold is located from the
geometry -- it is where a superblock's long span stops covering the BP code -- and
not asserted.
-/
theorem packedLongCrossoverIsAt5488 :
    Nat.min (2 * 5487) (GenericSelect.superLongSpan (2 * 5487)) = 2 * 5487 /\
      Nat.min (2 * 5488) (GenericSelect.superLongSpan (2 * 5488)) = 2 * 5488 /\
        Nat.min (2 * 5489) (GenericSelect.superLongSpan (2 * 5489)) < 2 * 5489 :=
  ⟨packedLongCrossover_before, packedLongCrossover_at, packedLongCrossover_after⟩

/--
The interior-readiness window, both endpoints with their neighbours. The clause
that moves is `macroSize <= blockCount`, and it moves because the summary base
jumps at `1024`.
-/
theorem packedInteriorWindowIs1024To1330 :
    packedInteriorMacroSize 1023 <= packedSummaryBlockCountRaw 1023 /\
      packedSummaryBlockCountRaw 1024 < packedInteriorMacroSize 1024 /\
        packedSummaryBlockCountRaw 1330 < packedInteriorMacroSize 1330 /\
          packedInteriorMacroSize 1331 <= packedSummaryBlockCountRaw 1331 :=
  packedInteriorReadinessWindow

/-! ## Stored and returned values fit one modeled word (`INV-WORD-WIDTH`) -/

/-- Every stored cell's value fits one modeled machine word. -/
theorem packedStoredCellValuesFitOneWord :
    forall (shape : Cartesian.CartesianShape) {cell : List Bool},
      cell ∈ packedMemory shape ->
        SuccinctSpace.bitsToNatLE cell < 2 ^ packedCellWidth shape.size :=
  packedStoredCellValue_lt_two_pow

/-- Every returned word's value fits one modeled machine word. -/
theorem packedReturnedWordValuesFitOneWord :
    forall (n bit width : Nat) (cells : List (List Bool)),
      width <= packedCellWidth n ->
        SuccinctSpace.bitsToNatLE (packedDecodeSpan n bit width cells) <
          2 ^ packedCellWidth n :=
  packedDecodedWordValue_lt_two_pow

/-! ## The executed store is a different object (`FG-08`, `INV-GLOBAL-PHYSICAL-MACHINE`)

Pinned here so the finding cannot be quietly dropped: it is the reason the
per-read lowering stops at executed segment 19.
-/

/-- The flat payload store and the executed store are not equal. -/
theorem packedExecutedStoreIsNotTheFlatPayloadStore :
    forall shape : Cartesian.CartesianShape,
      0 < packedSummaryBlockCount shape.size ->
        concreteBPNativeSuccinctRMQFlatPayloadReadStore shape ≠
          concreteBPNativeSuccinctRMQGlobalReadStore shape :=
  packedStoresNotEqual

/-- They disagree at a named address, not merely as objects. -/
theorem packedExecutedStoreDisagreesAtSegment23 :
    forall shape : Cartesian.CartesianShape,
      0 < packedSummaryBlockCount shape.size ->
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord? 23 0 ≠
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 23 0 :=
  packedStoresDisagree_atSegmentTwentyThree

/-! ## The header value is load-bearing for addresses (`FG-11`, `INV-VALUE-DEPENDENCY`)

The inequality is at an address, not at an enclosing trace record, which is the
distinction both rows insist on.
-/

/-- Changing only the decoded long count moves the flat offset of a source placed
after the long relative table. -/
theorem packedHeaderCountMovesTheOffset :
    forall (n : Nat) {lc1 lc2 : Nat}, lc1 ≠ lc2 ->
      packedSourceFlatOffset n lc1
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence ≠
        packedSourceFlatOffset n lc2
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence :=
  packedSourceFlatOffset_injective_longCount

/-- The same at the bit address the probe plan is computed from. -/
theorem packedHeaderCountMovesTheBitAddress :
    forall (n : Nat) {lc1 lc2 : Nat} (index stride : Nat), lc1 ≠ lc2 ->
      packedStridedBitAddress n lc1
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
          index stride ≠
        packedStridedBitAddress n lc2
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
          index stride :=
  packedStridedBitAddress_injective_longCount

/-- Changing only the header count changes the **issued probe cell**, not merely
the bit address. -/
theorem packedHeaderCountMovesTheIssuedCell :
    forall n lc index stride : Nat,
      packedStridedBitAddress n (lc + packedCellWidth n)
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
            index stride / packedCellWidth n ≠
        packedStridedBitAddress n lc
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLocalBaseOccurrence
            index stride / packedCellWidth n :=
  packedProbeCell_moves_with_longCount

/-!
Historical predecessor evidence only: the following unit-stride declarations
are preserved for regression history and are not imported into any `R2-*`
proposition or composition chain. The all-size controller section below has no
stride premise, sampled-size premise, or finite cutoff.
-/

/-! ## The sparse-exception path is unreachable at unit stride (`DD-20260804-041`) -/

/-- At unit stride a local slot's span is at most one occurrence wide. -/
theorem packedUnitStrideSpanIsAtMostOne :
    forall (bits : List Bool) (target : Bool) (slot : Nat),
      GenericSelect.localStride bits.length = 1 ->
        GenericSelect.shortSuperLocalSpan bits target slot <= 1 :=
  packedShortSuperLocalSpan_le_one_of_unit_stride

/--
No sparse exception can occur at unit stride: a one-occurrence span cannot exceed
a machine word.
-/
theorem packedNoSparseExceptionAtUnitStride :
    forall (bits : List Bool) (target : Bool) (slot : Nat),
      GenericSelect.localStride bits.length = 1 ->
        GenericSelect.localIsSparseException bits target slot = false :=
  packedLocalIsSparseException_false_of_unit_stride

/--
**The sparse relative table is empty at unit stride.** This is what dissolves the
one source whose word count was not a function of the input size and the header.
-/
theorem packedSparseRelativeTableIsEmptyAtUnitStride :
    forall (bits : List Bool) (target : Bool),
      GenericSelect.localStride bits.length = 1 ->
        GenericSelect.sparseExceptionRelativeEntries bits target = [] :=
  packedSparseExceptionEntries_nil_of_unit_stride

/--
At unit stride the sparse relative source answers nothing, so the capacity
over-approximation is never exercised: there is no index at which the packed read
and the store can disagree.
-/
theorem packedSparseRelativeSourceAnswersNothingAtUnitStride :
    forall (shape : Cartesian.CartesianShape) (index : Nat),
      GenericSelect.localStride shape.bpCode.length = 1 ->
        (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
          .selectSparseRelative)[index]? = none :=
  packedSparseRelativeWords_none_of_unit_stride

/-! ## The payload the accepted semantics consumes (`FG-01` re-target) -/

/-- The identity against the object the public `List Int` claim is stated about. -/
theorem packedReviewerPayloadIsTheAdvertisedPayload :
    forall xs : List Int,
      packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs) =
        SuccinctClassic.buildPayload xs :=
  packedReviewerPayloadBits_eq_buildPayload

/-- Its space clause and residual, preserving `FG-06`'s shape. -/
theorem packedReviewerPayloadSpaceBound :
    forall {n : Nat} {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (packedReviewerPayloadBits shape).length <=
          2 * n + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n :=
  packedReviewerPayloadBits_length_le

theorem packedReviewerOverheadIsLittleOLinear :
    SuccinctSpace.LittleOLinear
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead :=
  packedReviewerOverhead_littleO

/-!
## EG-CP-ALLSIZE-R1: exact-type consumers for the reviewer-memory controller

This section is the coordinator-amended validation surface for `R2-01` through
`R2-10`.  The declarations below intentionally restate concrete signatures and
propositions rather than adapting to whatever type a library declaration may
later have.  In particular, the executable controller has no shape, source
registry, semantic store, or answer-oracle argument; only its external driver
receives physical cell memory.
-/

/-! ### `R2-01` and `R2-03`: one consumed payload, header, and allocation -/

/-- The counted object is the canonical reviewer payload, not the flat sibling. -/
theorem egcpAllSizeConsumedPayloadIdentity :
    forall shape : CartesianShape,
      packedReviewerPayloadBits shape =
        concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape :=
  packedReviewerPayloadBits_eq_canonical

/-- The same exact object is the payload exposed by the public list builder. -/
theorem egcpAllSizeConsumedPayloadIsBuildPayload :
    forall xs : List Int,
      packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs) =
        SuccinctClassic.buildPayload xs :=
  packedReviewerPayloadBits_eq_buildPayload

/-- The accepted logical store is exactly the canonical reviewer store. -/
theorem egcpAllSizeConsumedStoreIdentity :
    forall (shape : CartesianShape) (segment index : Nat),
      (concreteBPNativeSuccinctRMQCanonicalReviewerReadStore shape).readWord?
          segment index =
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          segment index :=
  packedExecutedStore_is_reviewerStore

/-- The exact payload length depends only on the public size and two decoded counts. -/
def egcpAllSizeReviewerPayloadLengthSignature : Nat -> Nat -> Nat -> Nat :=
  @packedReviewerPayloadLength

/-- The executable closed length has the same shape-free three-scalar signature. -/
def egcpAllSizeClosedPayloadLengthSignature : Nat -> Nat -> Nat -> Nat :=
  @packedReviewerClosedPayloadLength

def egcpAllSizeClosedSourceOffsetSignature :
    Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat :=
  @packedReviewerClosedSourceOffset

/-- The closed arithmetic length is extensionally the counted reviewer length. -/
theorem egcpAllSizeClosedPayloadLengthIdentity :
    forall n longCount sparseCount : Nat,
      packedReviewerClosedPayloadLength n longCount sparseCount =
        packedReviewerPayloadLength n longCount sparseCount :=
  packedReviewerClosedPayloadLength_eq

/-- Exact all-size length of the actual counted payload. -/
theorem egcpAllSizeConsumedPayloadLength :
    forall shape : CartesianShape,
      (packedReviewerPayloadBits shape).length =
        packedReviewerPayloadLength shape.size (longCount shape)
          (packedReviewerSparseCount shape) :=
  packedReviewerPayloadBits_length_eq

/-- The one-cell header contains only `longCount`. -/
def egcpAllSizeHeaderSignature : CartesianShape -> List Bool :=
  @packedReviewerHeaderBits

theorem egcpAllSizeHeaderHasOneCellWidth :
    forall shape : CartesianShape,
      (packedReviewerHeaderBits shape).length =
        packedReviewerCellWidth shape.size :=
  packedReviewerHeaderBits_length

theorem egcpAllSizeHeaderDecodesLongCount :
    forall shape : CartesianShape,
      SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) =
        longCount shape :=
  packedReviewerHeaderBits_decode

/-- Dropping the single header recovers the counted payload with no interior pad. -/
theorem egcpAllSizeSerializedDropsToConsumedPayload :
    forall shape : CartesianShape,
      (packedReviewerSerializedBits shape).drop
          (packedReviewerCellWidth shape.size) =
        packedReviewerPayloadBits shape :=
  packedReviewerSerializedBits_drop_header

theorem egcpAllSizeSerializedLengthExact :
    forall shape : CartesianShape,
      (packedReviewerSerializedBits shape).length =
        packedReviewerCellWidth shape.size +
          packedReviewerPayloadLength shape.size (longCount shape)
            (packedReviewerSparseCount shape) :=
  packedReviewerSerializedBits_length

/-- The only padding is the final allocation suffix. -/
theorem egcpAllSizePaddedAllocationLengthExact :
    forall shape : CartesianShape,
      (packedReviewerPaddedBits shape).length =
        packedReviewerAllocatedBits shape.size (longCount shape)
          (packedReviewerSparseCount shape) :=
  packedReviewerPaddedBits_length

def egcpAllSizeReviewerMemorySignature : CartesianShape -> List (List Bool) :=
  @packedReviewerMemory

theorem egcpAllSizeReviewerMemoryCellCountExact :
    forall shape : CartesianShape,
      (packedReviewerMemory shape).length =
        packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) :=
  packedReviewerMemory_length

/-- Header and final-cell padding are both charged on the actual memory object. -/
theorem egcpAllSizeReviewerAllocatedSpace :
    forall shape : CartesianShape,
      (packedReviewerMemory shape).length *
          packedReviewerCellWidth shape.size <=
        2 * shape.size + packedReviewerRho shape.size :=
  packedReviewerMemory_length_mul_width_le

/-- The allocation residual itself is little-o linear. -/
theorem egcpAllSizeReviewerAllocationResidual :
    SuccinctSpace.LittleOLinear packedReviewerRho :=
  packedReviewerRho_littleO

/-! ### `R2-02`: all-size K1 sparse-count recovery -/

/-- K1 decodes only the public size and three prior physical replies. -/
def egcpAllSizeSparseCountDecoderSignature :
    Nat -> List Bool -> List Bool -> List Bool -> Nat :=
  @packedReviewerSparseCountFromReplies

def egcpAllSizeSparsePreludeNextSignature :
    PackedReviewerSparsePreludeState ->
      Option PackedReviewerSparsePreludeRequest :=
  @packedReviewerSparsePreludeNextRequest

def egcpAllSizeSparsePreludeConsumeSignature :
    PackedReviewerSparsePreludeState -> List Bool ->
      PackedReviewerSparsePreludeState :=
  @packedReviewerSparsePreludeConsumeReply

/-- The K1 request universe and order are exactly the three rank-at-end reads. -/
theorem egcpAllSizeSparsePreludeRequestSequence :
    forall n : Nat,
      packedReviewerSparsePreludeRequests n =
        [ .rankSuper, .rankBlock, .flagWord ] := by
  intro n
  rfl

/-- Prelude addresses are chosen before, and independently of, `sparseCount`. -/
theorem egcpAllSizeSparsePreludeAddressesIndependentOfSparseCount :
    forall n longCount sparseCountLeft sparseCountRight : Nat,
      packedReviewerSparsePreludeProbePlanAt n longCount sparseCountLeft =
        packedReviewerSparsePreludeProbePlanAt n longCount sparseCountRight :=
  packedReviewerSparsePreludeProbePlan_sparseCount_independent

/-- Three canonical reviewer-memory reads recover the exact count at every size. -/
theorem egcpAllSizeSparsePreludeExact :
    forall shape : CartesianShape,
      packedReviewerSparsePreludeRunAgainstMemory shape.size (longCount shape)
          (packedReviewerMemory shape) =
        some (packedReviewerSparseCount shape) :=
  packedReviewerSparsePreludeRunAgainstMemory_exact

/--
The final controller itself executes the three K1 plans, in source order, and
then enters the canonical whole-query state with a 210-read fuel budget (and
therefore at most 210 actual logical reads).  This is the load-bearing
prelude trace statement; the auxiliary sparse-prelude wrapper is deliberately
not used as final-run evidence.
-/
theorem egcpAllSizeActualControllerPrelude :
    forall (shape : CartesianShape) (left right wholeFuel : Nat),
      let superState :=
        packedReviewerSparsePreludeInit shape.size (longCount shape)
      packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
          ((packedReviewerSparsePreludeRequestPlan shape.size
              (longCount shape) .rankSuper).length +
            ((packedReviewerSparsePreludeRequestPlan shape.size
                (longCount shape) .rankBlock).length +
              ((packedReviewerSparsePreludeRequestPlan shape.size
                  (longCount shape) .flagWord).length + wholeFuel)))
          (packedReviewerNormalizePrelude 3 shape.size left right
            (longCount shape) superState) =
        packedReviewerPrependPhysicalEvents
          (packedReviewerSparsePreludePhysicalTrace shape)
          (packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
            wholeFuel
            (packedReviewerNormalizeWhole 210 shape.size left right
              (longCount shape) (packedReviewerSparseCount shape)
              (packedReviewerWholeStart shape.size left right))) :=
  packedReviewerDriveCanonicalPrelude_eq

/-! ### `R2-04`: all eight ragged segment-20 components -/

/-- Adding or removing an interior component makes this exhaustive consumer fail. -/
theorem egcpAllSizeInteriorComponentsAreExactlyEight
    (component : PackedReviewerInteriorComponentTag) :
    component = .baseline \/ component = .minRel \/ component = .maxRel \/
      component = .argOffset \/ component = .localOffset \/
      component = .globalBlock \/ component = .localLevel \/
      component = .globalLevel := by
  cases component <;> simp

/-- Component identity, entry/chunk coordinates, and the short final width. -/
theorem egcpAllSizeInteriorCoordinates :
    forall (n : Nat) (component : PackedReviewerInteriorComponentTag)
        (localWordIndex : Nat),
      let location :=
        packedReviewerInteriorLocation n component localWordIndex
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
          min (width - location.chunkIndex * wordSize) wordSize :=
  packedReviewerInteriorLocation_coordinates

/-- The tagged append prefix preserves the component word at its exact position. -/
theorem egcpAllSizeInteriorWordOrder :
    forall (shape : CartesianShape)
        (component : PackedReviewerInteriorComponentTag)
        (localWordIndex : Nat),
      localWordIndex <
          (packedReviewerInteriorCanonicalWords shape component).length ->
        (packedInteriorStoreWords shape)[
            packedReviewerInteriorComponentWordPrefix shape.size component +
              localWordIndex]? =
          (packedReviewerInteriorCanonicalWords shape component)[
            localWordIndex]? :=
  packedReviewerInteriorStoreAccess

/-- Every component word is exactly its entry-local, possibly short final chunk. -/
theorem egcpAllSizeInteriorCanonicalWord :
    forall (shape : CartesianShape)
        (component : PackedReviewerInteriorComponentTag)
        (localWordIndex : Nat),
      localWordIndex <
          (packedReviewerInteriorCanonicalWords shape component).length ->
        (packedReviewerInteriorCanonicalWords shape component)[localWordIndex]? =
          some (((packedReviewerInteriorCanonicalPayload shape component).drop
            (packedReviewerInteriorLocation shape.size component
              localWordIndex).bitOffset).take
            (packedReviewerInteriorLocation shape.size component
              localWordIndex).readWidth) :=
  packedReviewerInteriorCanonicalWord

/-- Component-local reviewer-memory decoding is exact for every tagged word. -/
theorem egcpAllSizeInteriorPhysicalDecode :
    forall (shape : CartesianShape)
        (component : PackedReviewerInteriorComponentTag)
        (localWordIndex : Nat),
      localWordIndex <
          (packedReviewerInteriorCanonicalWords shape component).length ->
        let location :=
          packedReviewerInteriorLocation shape.size component localWordIndex
        (packedFetch (packedReviewerMemory shape)
            (packedReviewerInteriorLocationPlan shape.size (longCount shape)
              (packedReviewerSparseCount shape) location)).map
          (packedReviewerDecodeSpan shape.size
            (packedReviewerInteriorBitAddress shape.size (longCount shape)
              (packedReviewerSparseCount shape) location)
            location.readWidth) =
          some (((packedReviewerInteriorCanonicalPayload shape component).drop
            location.bitOffset).take location.readWidth) :=
  packedReviewerInteriorLocationDecode

/-- Aggregate segment 20 is exactly the executed logical store, including `none`. -/
theorem egcpAllSizeSegment20Exact :
    forall (shape : CartesianShape) (index : Nat),
      packedReviewerInteriorRead shape.size (longCount shape)
          (packedReviewerSparseCount shape) (packedReviewerMemory shape) index =
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 index :=
  packedReviewerInteriorRead_eq_segment20

/-- Non-BP legacy requests are concretely routed through closed arithmetic. -/
theorem egcpAllSizeLegacyPlanIsClosed :
    forall (n longCount sparseCount : Nat)
        (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat),
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode ->
        source !=
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias ->
          packedReviewerLegacyRawPlan n longCount sparseCount source index =
            packedReviewerClosedSourceReadPlan n longCount sparseCount source
              index :=
  packedReviewerLegacyRawPlan_eq_closed

/-- Its decoder uses the same closed source address and the exact reply cells. -/
theorem egcpAllSizeLegacyDecodeIsClosed :
    forall (n longCount sparseCount : Nat)
        (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource) (index : Nat)
        (cells : List (List Bool)),
      source != ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode ->
        source !=
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.finalRankBPCodeAlias ->
          packedReviewerLegacyDecode n longCount sparseCount source index cells =
            packedReviewerDecodeSpan n
              (packedReviewerClosedStridedBitAddress n longCount source index
                (packedSourceStride n source))
              (packedReviewerSourceReadWidth n longCount sparseCount source
                index)
              cells :=
  packedReviewerLegacyDecode_eq_closed

/-- Executed segment 20's total logical plan is the ragged closed plan. -/
theorem egcpAllSizeSegment20LogicalPlan :
    forall (n longCount sparseCount : Nat)
        (request : PackedReviewerLogicalRequest),
      request.segment = 20 ->
        packedReviewerLogicalPlan n longCount sparseCount request =
          packedReviewerInteriorReadPlan n longCount sparseCount
            request.index :=
  packedReviewerLogicalPlan_segment20_eq

/-- Executed segment 20's total decoder is the classified ragged decoder. -/
theorem egcpAllSizeSegment20LogicalDecode :
    forall (n longCount sparseCount : Nat)
        (request : PackedReviewerLogicalRequest) (cells : List (List Bool)),
      request.segment = 20 ->
        packedReviewerLogicalDecode n longCount sparseCount request cells =
          match packedReviewerInteriorClassify n request.index with
          | none => none
          | some location =>
              some (packedReviewerDecodeSpan n
                (packedReviewerInteriorBitAddress n longCount sparseCount
                  location)
                location.readWidth cells) :=
  packedReviewerLogicalDecode_segment20_eq

/-! ### `R2-05` and `R2-06`: the first-order controller and memory-only driver -/

/-- Exact proof-free state constructors; adding shape/store/oracle fields breaks these. -/
def egcpAllSizeControllerHeaderStateSignature :
    Nat -> Nat -> Nat -> PackedReviewerControllerState :=
  @PackedReviewerControllerState.header

def egcpAllSizeControllerPreludeReadyStateSignature :
    Nat -> Nat -> Nat -> Nat -> PackedReviewerSparsePreludeState ->
      PackedReviewerControllerState :=
  @PackedReviewerControllerState.preludeReady

def egcpAllSizeControllerPreludeProbeStateSignature :
    Nat -> Nat -> Nat -> Nat -> PackedReviewerSparsePreludeState -> Nat ->
      List (List Bool) -> PackedReviewerControllerState :=
  @PackedReviewerControllerState.preludeProbe

def egcpAllSizeControllerWholeReadyStateSignature :
    Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> PackedReviewerWholeState ->
      PackedReviewerControllerState :=
  @PackedReviewerControllerState.wholeReady

def egcpAllSizeControllerWholeProbeStateSignature :
    Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> PackedReviewerWholeState -> Nat ->
      List (List Bool) -> PackedReviewerControllerState :=
  @PackedReviewerControllerState.wholeProbe

def egcpAllSizeControllerDoneStateSignature :
    Option Nat -> PackedReviewerControllerState :=
  @PackedReviewerControllerState.done

def egcpAllSizeControllerFailedState : PackedReviewerControllerState :=
  PackedReviewerControllerState.failed

def egcpAllSizePhysicalRequestConstructorSignature :
    PackedReviewerPhysicalOrigin -> Nat -> Nat -> Nat ->
      PackedReviewerPhysicalRequest :=
  @PackedReviewerPhysicalRequest.mk

def egcpAllSizePhysicalEventConstructorSignature :
    PackedReviewerPhysicalRequest -> Option (List Bool) ->
      PackedReviewerPhysicalEvent :=
  @PackedReviewerPhysicalEvent.mk

/-- The run stores only outcome, failure, residual state, and the actual trace. -/
def egcpAllSizeRunConstructorSignature :
    Option (Option Nat) -> Bool -> PackedReviewerControllerState ->
      List PackedReviewerPhysicalEvent -> PackedReviewerRun :=
  @PackedReviewerRun.mk

def egcpAllSizeControllerSignature :
    Nat -> Nat -> Nat -> PackedReviewerControllerState :=
  @packedReviewerController

def egcpAllSizeNextRequestSignature :
    PackedReviewerControllerState -> Option PackedReviewerPhysicalRequest :=
  @packedReviewerNextRequest

def egcpAllSizeConsumeReplySignature :
    PackedReviewerControllerState -> Option (List Bool) ->
      PackedReviewerControllerState :=
  @packedReviewerConsumeReply

def egcpAllSizeControllerResultSignature :
    PackedReviewerControllerState -> Option (Option Nat) :=
  @packedReviewerControllerResult

def egcpAllSizeControllerFailedSignature :
    PackedReviewerControllerState -> Bool :=
  @packedReviewerControllerFailed

/-- Valid half-open endpoints enter the physical header phase exactly. -/
theorem egcpAllSizeValidControllerEntry
    (n left right : Nat) (hvalid : left < right ∧ right <= n) :
    packedReviewerController n left right = .header n left right := by
  simp [packedReviewerController, hvalid]

/-- Empty, reversed, and out-of-range endpoints are terminal before any read. -/
theorem egcpAllSizeInvalidControllerEntry
    (n left right : Nat) (hbad : ¬ (left < right ∧ right <= n)) :
    packedReviewerController n left right = .done none := by
  simp [packedReviewerController, hbad]

/-- The invalid public route has no decorative or unreachable child requests. -/
theorem egcpAllSizeInvalidRunHasZeroTrace
    (memory : List (List Bool)) (n left right : Nat)
    (hbad : ¬ (left < right ∧ right <= n)) :
    packedReviewerRunAgainstMemory memory n left right =
      { terminal := some none
        failed := false
        state := .done none
        trace := [] } := by
  simp [packedReviewerRunAgainstMemory, packedReviewerController, hbad,
    packedReviewerControllerMeasure, packedReviewerDriveAgainstMemoryAux,
    packedReviewerControllerResult, packedReviewerControllerFailed]

/-- Cell zero is the first and only header request. -/
theorem egcpAllSizeHeaderNextRequest (n left right : Nat) :
    packedReviewerNextRequest (.header n left right) =
      some
        { origin := .header
          address := 0
          ordinal := 0
          cellCount := 1 } :=
  rfl

/-- A missing physical reply is a real driver failure, not a semantic fallback. -/
theorem egcpAllSizeMissingReplyFails
    (state : PackedReviewerControllerState) :
    packedReviewerConsumeReply state none = .failed := by
  cases state <;> rfl

/-- The executable address table uses only size, decoded counts, and a request. -/
def egcpAllSizeLogicalPlanSignature :
    Nat -> Nat -> Nat -> PackedReviewerLogicalRequest -> List Nat :=
  @packedReviewerLogicalPlan

/-- Decoding adds only the physical replies already received. -/
def egcpAllSizeLogicalDecodeSignature :
    Nat -> Nat -> Nat -> PackedReviewerLogicalRequest -> List (List Bool) ->
      Option (List Bool) :=
  @packedReviewerLogicalDecode

/-- The driver accepts physical memory, never a `WordRAM.ReadStore`. -/
def egcpAllSizeRunAgainstMemorySignature :
    List (List Bool) -> Nat -> Nat -> Nat -> PackedReviewerRun :=
  @packedReviewerRunAgainstMemory

/-- Every event reply is the literal lookup made in the supplied memory. -/
theorem egcpAllSizeDriverMemoryOnly :
    forall (memory : List (List Bool)) (n left right : Nat) event,
      event ∈ (packedReviewerRunAgainstMemory memory n left right).trace ->
        event.reply = memory[event.request.address]? :=
  packedReviewerRunAgainstMemory_memory_only

/-- Ordered agreement on the first run determines the entire second run object. -/
theorem egcpAllSizeDynamicStoreAgreement :
    forall (memoryA memoryB : List (List Bool)) (n left right : Nat),
      (forall event,
        event ∈
            (packedReviewerDriveAgainstMemoryAux memoryA
              (packedReviewerControllerMeasure
                (packedReviewerController n left right))
              (packedReviewerController n left right)).trace ->
          memoryB[event.request.address]? = event.reply) ->
        packedReviewerRunAgainstMemory memoryA n left right =
          packedReviewerRunAgainstMemory memoryB n left right :=
  by
    intro memoryA memoryB n left right hagree
    exact packedReviewerRunAgainstMemory_eq_of_agree memoryA memoryB n
      left right (by
        simpa [PackedReviewerMemoriesAgreeOnRun] using hagree)

/-! ### `R2-07`: ordered logical and physical lowering -/

/-- No disconnected physical trace may be supplied to the grouping target. -/
def egcpAllSizeExpectedPhysicalTraceSignature :
    CartesianShape -> Nat -> Nat -> List PackedReviewerPhysicalEvent :=
  @packedReviewerExpectedPhysicalTrace

/-- Every logical segment is answered from the identical reviewer memory. -/
theorem egcpAllSizeEveryLogicalReadFromReviewerMemory :
    forall (shape : CartesianShape) (request : PackedReviewerLogicalRequest),
      packedReviewerLogicalRead shape.size (longCount shape)
          (packedReviewerSparseCount shape) (packedReviewerMemory shape)
          request =
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index :=
  packedReviewerLogicalRead_eq_globalReadStore

/-- Ordered logical simulation fixes result, state, and every reference event. -/
theorem egcpAllSizeLogicalWholeRunSimulation :
    forall (shape : CartesianShape) (left right : Nat),
      left < right -> right <= shape.size ->
        let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
        let run :=
          packedReviewerDriveLogical store 210
            (packedReviewerWholeStart shape.size left right)
        let reference := packedWholeQueryRun store shape.size left right
        run.terminal = some reference.value /\
          run.state = .done reference.value /\
          run.trace.map PackedReviewerLogicalEvent.erase = reference.trace :=
  packedReviewerDriveLogical_210_simulates_packedWholeQueryRun

/-- Equal repeated reads retain their global logical occurrence. -/
theorem egcpAllSizeLogicalOccurrenceSimulation :
    forall (shape : CartesianShape) (left right : Nat),
      left < right -> right <= shape.size ->
        forall (position : Nat) (event : PackedReviewerLogicalEvent),
          (packedReviewerDriveLogical
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
            (packedReviewerWholeStart shape.size left right)).trace[position]? =
              some event ->
            (packedWholeQueryRun
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              shape.size left right).trace[position]? =
              some event.erase :=
  packedReviewerDriveLogical_210_occurrence_erases

/--
The canonical logical run and the occurrence-expanded physical trace are the
two projections of one lowered run object.
-/
theorem egcpAllSizeLoweredWholeRunSimulation :
    forall (shape : CartesianShape) (left right : Nat),
      left < right -> right <= shape.size ->
        let lowered :=
          packedReviewerDriveLoweredWhole shape 210
            (packedReviewerWholeStart shape.size left right)
        let reference :=
          packedWholeQueryRun
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            shape.size left right
        lowered.terminal = some reference.value /\
          lowered.state = .done reference.value /\
          lowered.logicalTrace.map PackedReviewerLogicalEvent.erase =
            reference.trace /\
          lowered.physicalTrace =
            packedReviewerLogicalTracePhysicalTrace shape
              lowered.logicalTrace :=
  packedReviewerDriveLoweredWhole_210_simulates_packedWholeQueryRun

/-- Per-plan physical expansion retains address, reply, ordinal, and multiplicity. -/
theorem egcpAllSizePhysicalOccurrenceExpansion :
    forall (memory : List (List Bool))
        (origin : PackedReviewerPhysicalOrigin) (plan : List Nat)
        (position : Nat),
      (packedReviewerPhysicalEvents memory origin plan)[position]? =
        plan[position]?.map fun address =>
          { request :=
              { origin := origin
                address := address
                ordinal := position
                cellCount := plan.length }
            reply := memory[address]? } :=
  packedReviewerPhysicalEvents_get?_eq

/-- The actual valid run is header, K1, then the lowered whole run in order. -/
theorem egcpAllSizeActualRunLowering :
    forall (shape : CartesianShape) (left right : Nat),
      left < right ∧ right <= shape.size ->
        let lowered :=
          packedReviewerDriveLoweredWhole shape 210
            (packedReviewerWholeStart shape.size left right)
        packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right =
          packedReviewerPrependPhysicalEvents
            (packedReviewerHeaderPhysicalTrace shape)
            (packedReviewerPrependPhysicalEvents
              (packedReviewerSparsePreludePhysicalTrace shape)
              (packedReviewerRunOfLowered lowered)) :=
  packedReviewerRunAgainstMemory_eq_lowered

/-- The grouping equality is about the actual run, not an auxiliary trace. -/
theorem egcpAllSizeActualRunGrouping
    (shape : CartesianShape) (left right : Nat)
    (grouping : PackedReviewerRunGrouping shape left right) :
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace =
      packedReviewerExpectedPhysicalTrace shape left right :=
  grouping.trace_eq

/--
The global physical occurrence is pinned independently: repeated equal cells
remain distinguished by their position in the actual run and in the exact
header/K1/logical expansion.
-/
theorem egcpAllSizeActualRunPhysicalOccurrence
    {shape : CartesianShape} {left right position : Nat}
    (grouping : PackedReviewerRunGrouping shape left right) :
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace[position]? =
      (packedReviewerExpectedPhysicalTrace shape left right)[position]? :=
  grouping.get?_eq position

/-! ### `R2-08` and `R2-09`: totality, capacity, cap, and public semantics -/

/--
The initial physical budget is structural.  Replacing this arm by a stored
literal `427` breaks the consumer even if a later inequality still happens to
compile.
-/
theorem egcpAllSizeHeaderMeasureIsStructural (n left right : Nat) :
    packedReviewerControllerMeasure (.header n left right) =
      1 +
        2 * packedReviewerSparsePreludeRemaining
          (packedReviewerSparsePreludeInit n 0) +
        2 * packedReviewerWholeRemaining
          (packedReviewerWholeStart n left right) :=
  rfl

/-- The literal cap is derived for the actual run and is not a state field. -/
theorem egcpAllSizeActualRunProbeCap :
    forall (memory : List (List Bool)) (n left right : Nat),
      (packedReviewerRunAgainstMemory memory n left right).trace.length <= 427 :=
  packedReviewerRunAgainstMemory_trace_length_le_427

/-- The same literal cap is also derived through the reconstructed run grouping. -/
theorem egcpAllSizeGroupedActualRunProbeCap :
    forall {shape : CartesianShape} {left right : Nat},
      PackedReviewerRunGrouping shape left right ->
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace.length <= 427 :=
  by
    intro shape left right grouping
    exact grouping.trace_length_le_427

/-- Every grouped actual request is allocated in the same reviewer memory. -/
theorem egcpAllSizeActualRunAllocated :
    forall {shape : CartesianShape} {left right : Nat},
      PackedReviewerRunGrouping shape left right ->
        forall {event : PackedReviewerPhysicalEvent},
          event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).trace ->
            event.request.address <
              packedReviewerCellCount shape.size (longCount shape)
                (packedReviewerSparseCount shape) :=
  PackedReviewerRunGrouping.address_lt_cellCount

/-- Every grouped actual request fits the query-independent address width. -/
theorem egcpAllSizeActualRunAddressWidth :
    forall {shape : CartesianShape} {left right : Nat},
      PackedReviewerRunGrouping shape left right ->
        forall {event : PackedReviewerPhysicalEvent},
          event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).trace ->
            event.request.address < 2 ^ packedReviewerCellWidth shape.size :=
  PackedReviewerRunGrouping.address_lt_two_pow

/-- Every retained logical instruction/site/segment/index operand fits one word. -/
theorem egcpAllSizeCanonicalLogicalRequestOperandsWidth :
    forall (shape : CartesianShape) (left right : Nat),
      left < right -> right <= shape.size ->
        forall event,
          event ∈
              (packedReviewerDriveLogical
                (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
                (packedReviewerWholeStart shape.size left right)).trace ->
            PackedReviewerLogicalRequestOperandsFit shape.size event.request :=
  packedReviewerDriveLogical_210_request_operands_fit

/-- Every actual physical origin/address/ordinal/count operand fits one word. -/
theorem egcpAllSizeActualPhysicalRequestOperandsWidth :
    forall {shape : CartesianShape} {left right : Nat},
      PackedReviewerRunGrouping shape left right ->
        forall {event : PackedReviewerPhysicalEvent},
          event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).trace ->
              PackedReviewerPhysicalRequestOperandsFit shape.size
                event.request :=
  PackedReviewerRunGrouping.request_operands_fit

/-- Fixed instruction and read-site tags have explicit all-size encodings. -/
theorem egcpAllSizeLogicalControlTagsWidth :
    forall (n : Nat) (request : PackedReviewerLogicalRequest),
      PackedReviewerLogicalControlCodesFit n request :=
  packedReviewerLogicalControlCodes_fit

/-- Header, K1, and whole-query physical origins retain explicit tag encodings. -/
theorem egcpAllSizePhysicalControlTagsWidth :
    forall (n : Nat) (origin : PackedReviewerPhysicalOrigin),
      PackedReviewerPhysicalControlCodesFit n origin :=
  packedReviewerPhysicalControlCodes_fit

/-- Every one of the seven concrete top-level controller phases fits one word. -/
theorem egcpAllSizeControllerPhaseTagWidth :
    forall (n : Nat) (state : PackedReviewerControllerState),
      PackedReviewerNatFits n
        (packedReviewerControllerStatePhaseCode state) :=
  packedReviewerControllerStatePhaseCode_fits

/-- Every successful actual reply is exactly one reviewer-width cell. -/
theorem egcpAllSizeActualReplyWidth :
    forall (shape : CartesianShape) (left right : Nat)
        {event : PackedReviewerPhysicalEvent} {cell : List Bool},
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          cell.length = packedReviewerCellWidth shape.size :=
  packedReviewerRunAgainstMemory_reply_width

/-- Successful replies also fit numerically, not merely by list length. -/
theorem egcpAllSizeActualReplyValueWidth :
    forall (shape : CartesianShape) (left right : Nat)
        {event : PackedReviewerPhysicalEvent} {cell : List Bool},
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          SuccinctSpace.bitsToNatLE cell <
            2 ^ packedReviewerCellWidth shape.size :=
  packedReviewerRunAgainstMemory_reply_value_width

/-- The segment-20 failed/dead logical address also fits the same width. -/
theorem egcpAllSizeInteriorDeadAddressWidth :
    forall (n : Nat),
      (packedInteriorOffsets n).deadAddress <
        2 ^ packedReviewerCellWidth n :=
  packedReviewerInteriorDeadAddress_lt_two_pow

/-- The query-independent physical word width remains logarithmic in input size. -/
theorem egcpAllSizeReviewerWordWidthLogarithmic :
    forall (n : Nat),
      packedReviewerCellWidth n <= 20 * (Nat.log2 (n + 2) + 1) :=
  packedReviewerCellWidth_le_log

/-- The same physical run returns the independent guarded public semantics. -/
theorem egcpAllSizeSameRunPublicOutcome :
    forall (xs : List Int) (left right : Nat),
      let shape := SuccinctClassic.cartesianShape xs
      let run := packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right
      run.terminal =
          some (SuccinctClassic.queryTraceResult xs left right).value /\
        run.failed = false /\
        run.state =
          .done (SuccinctClassic.queryTraceResult xs left right).value /\
        PackedReviewerRunGrouping shape left right :=
  packedReviewerRunAgainstMemory_public_outcome

/-- Removing or weakening any public certificate field changes this exact type. -/
theorem egcpAllSizePublicCertificateExact :
    forall (xs : List Int) (left right : Nat),
      PackedReviewerPublicRunCertificate xs left right :=
  @packedReviewerRunAgainstMemory_public_certificate

/--
Independent same-object facts.  Unlike a consumer that merely repeats the
library certificate type, every field below restates the proposition over the
literal public payload, reviewer memory, and physical run.
-/
structure EGCPAllSizeIndependentRunFacts
    (xs : List Int) (left right : Nat) : Prop where
  payload_identity :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerPayloadBits shape = SuccinctClassic.buildPayload xs
  serialized_identity :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerSerializedBits shape).drop
      (packedReviewerCellWidth shape.size) = SuccinctClassic.buildPayload xs
  memory_length :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length =
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape)
  allocated_space :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <=
      2 * shape.size + packedReviewerRho shape.size
  terminal_eq :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value
  failed_false :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).failed = false
  state_eq :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).state =
        .done (SuccinctClassic.queryTraceResult xs left right).value
  grouping :
    PackedReviewerRunGrouping (SuccinctClassic.cartesianShape xs) left right
  invalid_no_requests :
    let shape := SuccinctClassic.cartesianShape xs
    ¬ (left < right ∧ right <= shape.size) ->
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace = []
  input_size_width :
    let shape := SuccinctClassic.cartesianShape xs
    shape.size < 2 ^ packedReviewerCellWidth shape.size
  valid_endpoints_width :
    let shape := SuccinctClassic.cartesianShape xs
    left < right ∧ right <= shape.size ->
      PackedReviewerNatFits shape.size left ∧
        PackedReviewerNatFits shape.size right
  header_values_width :
    let shape := SuccinctClassic.cartesianShape xs
    longCount shape < 2 ^ packedReviewerCellWidth shape.size ∧
      packedReviewerSparseCount shape <
        2 ^ packedReviewerCellWidth shape.size
  memory_words_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall cell, cell ∈ packedReviewerMemory shape ->
      PackedReviewerWordFits shape.size cell ∧
        SuccinctSpace.bitsToNatLE cell <
          2 ^ packedReviewerCellWidth shape.size
  prelude_decode_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall state request cells word,
      packedReviewerSparsePreludeNextRequest state = some request ->
        packedReviewerDecodePreludeReplies shape.size (longCount shape)
            state cells = some word ->
          PackedReviewerWordFits shape.size word
  logical_decode_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall request cells word,
      packedReviewerLogicalDecode shape.size (longCount shape)
          (packedReviewerSparseCount shape) request cells = some word ->
        PackedReviewerWordFits shape.size word
  logical_request_operands_width :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      forall event,
        event ∈
            (packedReviewerDriveLogical
              (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
              (packedReviewerWholeStart shape.size left right)).trace ->
          PackedReviewerLogicalRequestOperandsFit shape.size event.request
  logical_control_tags_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall request, PackedReviewerLogicalControlCodesFit shape.size request
  physical_control_tags_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall origin, PackedReviewerPhysicalControlCodesFit shape.size origin
  controller_phase_tag_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall state,
      PackedReviewerNatFits shape.size
        (packedReviewerControllerStatePhaseCode state)
  memory_only :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.reply = (packedReviewerMemory shape)[event.request.address]?
  reply_success :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        exists cell, event.reply = some cell
  allocated :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address <
          packedReviewerCellCount shape.size (longCount shape)
            (packedReviewerSparseCount shape)
  address_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address < 2 ^ packedReviewerCellWidth shape.size
  physical_request_operands_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        PackedReviewerPhysicalRequestOperandsFit shape.size event.request
  reply_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event cell,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          cell.length = packedReviewerCellWidth shape.size
  reply_value_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event cell,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          SuccinctSpace.bitsToNatLE cell <
            2 ^ packedReviewerCellWidth shape.size
  dead_address_width :
    let shape := SuccinctClassic.cartesianShape xs
    (packedInteriorOffsets shape.size).deadAddress <
      2 ^ packedReviewerCellWidth shape.size
  word_width_logarithmic :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerCellWidth shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  trace_cap :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427
  result_width :
    forall index,
      (SuccinctClassic.queryTraceResult xs left right).value = some index ->
        index <
          2 ^ packedReviewerCellWidth
            (SuccinctClassic.cartesianShape xs).size

/-- Every independent fact is inhabited by projections from the public proof. -/
theorem egcpAllSizeIndependentRunFactsExact
    (xs : List Int) (left right : Nat) :
    EGCPAllSizeIndependentRunFacts xs left right := by
  have hpayload := packedReviewerPayloadBits_eq_buildPayload xs
  have hserialized :=
    packedReviewerSerializedBits_drop_header
      (SuccinctClassic.cartesianShape xs)
  rw [hpayload] at hserialized
  have certificate :=
    packedReviewerRunAgainstMemory_public_certificate xs left right
  exact
    { payload_identity := hpayload
      serialized_identity := hserialized
      memory_length :=
        packedReviewerMemory_length (SuccinctClassic.cartesianShape xs)
      allocated_space :=
        packedReviewerMemory_length_mul_width_le
          (SuccinctClassic.cartesianShape xs)
      terminal_eq := certificate.terminal_eq
      failed_false := certificate.failed_false
      state_eq := certificate.state_eq
      grouping := certificate.grouping
      invalid_no_requests := certificate.invalid_no_requests
      input_size_width := certificate.input_size_width
      valid_endpoints_width := certificate.valid_endpoints_width
      header_values_width := certificate.header_values_width
      memory_words_width := certificate.memory_words_width
      prelude_decode_width := certificate.prelude_decode_width
      logical_decode_width := certificate.logical_decode_width
      logical_request_operands_width :=
        certificate.logical_request_operands_width
      logical_control_tags_width := certificate.logical_control_tags_width
      physical_control_tags_width := certificate.physical_control_tags_width
      controller_phase_tag_width := certificate.controller_phase_tag_width
      memory_only := certificate.memory_only
      reply_success := certificate.reply_success
      allocated := certificate.allocated
      address_width := certificate.address_width
      physical_request_operands_width :=
        certificate.physical_request_operands_width
      reply_width := certificate.reply_width
      reply_value_width := certificate.reply_value_width
      dead_address_width := certificate.dead_address_width
      word_width_logarithmic := certificate.word_width_logarithmic
      trace_cap := certificate.trace_cap
      result_width := certificate.result_width }

/--
One independent proposition pins payload, allocation, physical run, reference
result, grouping, backing, address capacity, reply width, and the literal cap on
the identical objects.  A sibling payload/memory/run substitution or weakened
certificate field does not inhabit this type.
-/
theorem egcpAllSizeIdenticalObjectPublicConsumer
    (xs : List Int) (left right : Nat) :
    let shape := SuccinctClassic.cartesianShape xs
    let payload := SuccinctClassic.buildPayload xs
    let memory := packedReviewerMemory shape
    let run := packedReviewerRunAgainstMemory memory shape.size left right
    packedReviewerPayloadBits shape = payload /\
      (packedReviewerSerializedBits shape).drop
          (packedReviewerCellWidth shape.size) = payload /\
      memory.length =
        packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape) /\
      run.terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value /\
      run.failed = false /\
      run.state =
        .done (SuccinctClassic.queryTraceResult xs left right).value /\
      PackedReviewerRunGrouping shape left right /\
      (forall event,
        event ∈ run.trace ->
          event.reply = memory[event.request.address]?) /\
      (forall event,
        event ∈ run.trace ->
          event.request.address <
            packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape)) /\
      (forall event,
        event ∈ run.trace ->
          event.request.address < 2 ^ packedReviewerCellWidth shape.size) /\
      (forall event cell,
        event ∈ run.trace ->
          event.reply = some cell ->
            cell.length = packedReviewerCellWidth shape.size) /\
      run.trace.length <= 427 /\
      (forall index,
        (SuccinctClassic.queryTraceResult xs left right).value = some index ->
          index < 2 ^ packedReviewerCellWidth shape.size) := by
  dsimp only
  have hpayload := packedReviewerPayloadBits_eq_buildPayload xs
  have hserialized :=
    packedReviewerSerializedBits_drop_header
      (SuccinctClassic.cartesianShape xs)
  rw [hpayload] at hserialized
  have hmemory :=
    packedReviewerMemory_length (SuccinctClassic.cartesianShape xs)
  have certificate :=
    packedReviewerRunAgainstMemory_public_certificate xs left right
  exact
    ⟨hpayload, hserialized, hmemory,
      certificate.terminal_eq, certificate.failed_false,
      certificate.state_eq, certificate.grouping,
      certificate.memory_only, certificate.allocated,
      certificate.address_width, certificate.reply_width,
      certificate.trace_cap, certificate.result_width⟩

/-!
The exact signatures above are the typed positive anti-bypass controls for
`R2-10`: a controller shape parameter, an answer-oracle parameter, a supplied
`WordRAM.ReadStore`, a sibling memory, a weakened grouping/correctness field, or
a forged non-`427` cap changes one of these independently written expected types
and therefore breaks this validation root.
-/

/-! ### Stage-F residual campaign: the combined capstone (`FG-13`)

`EGCPStageFCapstoneFacts` restates every frozen capstone conjunct
independently over the literal public payload, reviewer memory, and physical
run, and `egcpStageFCapstoneFactsExact` discharges it by projection from
`packedReviewerStageFCapstone_holds`.  Removing or weakening any capstone
conjunct breaks this structure's producer rather than being absorbed by it.
-/

/-- The Stage-F capstone's exact shape, pinned as a signature. -/
def egcpStageFCapstoneSignature : List Int -> Nat -> Nat -> Prop :=
  @PackedReviewerStageFCapstone

/-- Independent restatement of the twelve frozen Stage-F conjuncts. -/
structure EGCPStageFCapstoneFacts
    (xs : List Int) (left right : Nat) : Prop where
  payload_is_buildPayload :
    packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs) =
      SuccinctClassic.buildPayload xs
  serialized_header_payload :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerSerializedBits shape =
      packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape
  padded_final_padding :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerPaddedBits shape =
        packedReviewerSerializedBits shape ++
          List.replicate
            (packedReviewerAllocatedBits shape.size (longCount shape)
                (packedReviewerSparseCount shape) -
              (packedReviewerSerializedBits shape).length) false /\
      (packedReviewerPaddedBits shape).length =
        packedReviewerAllocatedBits shape.size (longCount shape)
          (packedReviewerSparseCount shape)
  one_cell_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall cell, cell ∈ packedReviewerMemory shape ->
      cell.length = packedReviewerCellWidth shape.size
  allocation_two_n_plus_rho :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <=
      2 * shape.size + packedReviewerRho shape.size
  rho_little_o : SuccinctSpace.LittleOLinear packedReviewerRho
  probes_backed_by_memory :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.reply = (packedReviewerMemory shape)[event.request.address]?
  probes_allocated_and_successful :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address <
            packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape) /\
          exists cell, event.reply = some cell
  ordered_grouping :
    PackedReviewerRunGrouping (SuccinctClassic.cartesianShape xs) left right
  derived_cap_427 :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427
  guarded_reference_result :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).terminal =
          some (SuccinctClassic.queryTraceResult xs left right).value /\
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).failed = false /\
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).state =
          .done (SuccinctClassic.queryTraceResult xs left right).value
  controller_input_boundary :
    let shape := SuccinctClassic.cartesianShape xs
    @packedReviewerController =
        (fun (n left right : Nat) => packedReviewerController n left right) /\
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right =
        packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
          (packedReviewerControllerMeasure
            (packedReviewerController shape.size left right))
          (packedReviewerController shape.size left right)
  closed_length_and_memory_arity :
    let shape := SuccinctClassic.cartesianShape xs
    (forall n longCount sparseCount : Nat,
        packedReviewerClosedPayloadLength n longCount sparseCount =
          packedReviewerPayloadLength n longCount sparseCount) /\
      (packedReviewerMemory shape).length =
        packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape)
  store_agreement_determinism :
    let shape := SuccinctClassic.cartesianShape xs
    forall memoryB : List (List Bool),
      (forall event,
        event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
          memoryB[event.request.address]? = event.reply) ->
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right =
        packedReviewerRunAgainstMemory memoryB shape.size left right

/-- Every independent Stage-F fact is inhabited by capstone projection. -/
theorem egcpStageFCapstoneFactsExact
    (xs : List Int) (left right : Nat) :
    EGCPStageFCapstoneFacts xs left right := by
  have capstone := packedReviewerStageFCapstone_holds xs left right
  exact
    { payload_is_buildPayload := capstone.payload_is_buildPayload
      serialized_header_payload := capstone.serialized_header_payload
      padded_final_padding := capstone.padded_final_padding
      one_cell_width := capstone.one_cell_width
      allocation_two_n_plus_rho := capstone.allocation_two_n_plus_rho
      rho_little_o := capstone.rho_little_o
      probes_backed_by_memory := capstone.probes_backed_by_memory
      probes_allocated_and_successful :=
        capstone.probes_allocated_and_successful
      ordered_grouping := capstone.ordered_grouping
      derived_cap_427 := capstone.derived_cap_427
      guarded_reference_result := capstone.guarded_reference_result
      controller_input_boundary := capstone.controller_input_boundary
      closed_length_and_memory_arity :=
        capstone.closed_length_and_memory_arity
      store_agreement_determinism :=
        capstone.store_agreement_determinism }

/-! ### Stage-F residual campaign: `FG-11` header liveness

The expected type below is written out in full: the two projections are the
`trace[1]` request addresses of the canonical and the header-mutated runs of
the identical driver, and the conclusion is their inequality.  A retreat to
an enclosing-record inequality, or to a sampled size, no longer inhabits this
type.
-/

/-- Replacing only the counted long-count header cell moves the second
attempted physical address, for every shape and every valid query. -/
theorem egcpStageFHeaderAddressLiveness :
    forall (shape : CartesianShape) (left right : Nat),
      left < right -> right <= shape.size ->
        exists addressCanonical addressMutated,
          ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
              shape.size left right).trace.map
                (fun event => event.request.address))[1]? =
              some addressCanonical /\
          ((packedReviewerRunAgainstMemory
              ((packedReviewerMemory shape).set 0
                (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
                  (longCount shape + packedReviewerCellWidth shape.size)))
              shape.size left right).trace.map
                (fun event => event.request.address))[1]? =
              some addressMutated /\
          addressCanonical ≠ addressMutated :=
  fun shape left right hleft hright =>
    packedReviewerHeaderCellAddressLiveness shape left right hleft hright

/-- The canonical run opens with the header probe at cell zero. -/
theorem egcpStageFRunOpensWithHeader :
    forall (shape : CartesianShape) (left right : Nat),
      left < right -> right <= shape.size ->
        ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).trace.map
              (fun event => event.request.address))[0]? = some 0 :=
  fun shape left right hleft hright =>
    packedReviewerRunOpensWithHeader shape left right hleft hright

/-! ### Stage-F residual campaign: `FG-14` boundary instances

Every instance is the one universal capstone instantiated; the geometry
thresholds themselves are pinned by the `Boundaries.lean` consumers earlier
in this file, and the six-size readiness-window neighbour fact is added
here.
-/

/-- Empty, singleton, and both size-two shapes inhabit the capstone. -/
theorem egcpStageFSmallSizeInstances :
    PackedReviewerStageFCapstone [] 0 0 /\
      PackedReviewerStageFCapstone [0] 0 1 /\
      PackedReviewerStageFCapstone [0, 1] 0 2 /\
      PackedReviewerStageFCapstone [1, 0] 0 2 :=
  ⟨packedReviewerStageFCapstone_empty,
    packedReviewerStageFCapstone_singleton,
    packedReviewerStageFCapstone_sizeTwoLeft,
    packedReviewerStageFCapstone_sizeTwoRight⟩

/-- The two size-two shapes are distinct, witnessed by diverging answers. -/
theorem egcpStageFSizeTwoDistinct :
    SuccinctClassic.cartesianShape [(0 : Int), 1] ≠
      SuccinctClassic.cartesianShape [(1 : Int), 0] :=
  packedReviewerStageFCapstone_sizeTwoShapesDistinct

/-- The long crossover triple inhabits the capstone. -/
theorem egcpStageFCrossoverInstances :
    PackedReviewerStageFCapstone (List.replicate 5487 0) 0 5487 /\
      PackedReviewerStageFCapstone (List.replicate 5488 0) 0 5488 /\
      PackedReviewerStageFCapstone (List.replicate 5489 0) 0 5489 :=
  ⟨packedReviewerStageFCapstone_crossover5487,
    packedReviewerStageFCapstone_crossover5488,
    packedReviewerStageFCapstone_crossover5489⟩

/-- The readiness window's six sizes inhabit the capstone. -/
theorem egcpStageFReadinessWindowInstances :
    PackedReviewerStageFCapstone (List.replicate 1023 0) 0 1023 /\
      PackedReviewerStageFCapstone (List.replicate 1024 0) 0 1024 /\
      PackedReviewerStageFCapstone (List.replicate 1025 0) 0 1025 /\
      PackedReviewerStageFCapstone (List.replicate 1329 0) 0 1329 /\
      PackedReviewerStageFCapstone (List.replicate 1330 0) 0 1330 /\
      PackedReviewerStageFCapstone (List.replicate 1331 0) 0 1331 :=
  packedReviewerStageFCapstone_readinessWindow

/-- The readiness clause moves across the window while the capstone statement
does not: both endpoints and both neighbours, kernel-checked. -/
theorem egcpStageFReadinessNeighbors :
    packedInteriorMacroSize 1023 <= packedSummaryBlockCountRaw 1023 /\
      packedSummaryBlockCountRaw 1024 < packedInteriorMacroSize 1024 /\
      packedSummaryBlockCountRaw 1025 < packedInteriorMacroSize 1025 /\
      packedSummaryBlockCountRaw 1329 < packedInteriorMacroSize 1329 /\
      packedSummaryBlockCountRaw 1330 < packedInteriorMacroSize 1330 /\
      packedInteriorMacroSize 1331 <= packedSummaryBlockCountRaw 1331 :=
  packedInteriorReadinessWindowNeighbors

/-- Empty-range, reversed, and out-of-range queries inhabit the capstone. -/
theorem egcpStageFInvalidQueryInstances :
    PackedReviewerStageFCapstone [7, 3, 3] 1 1 /\
      PackedReviewerStageFCapstone [7, 3, 3] 2 1 /\
      PackedReviewerStageFCapstone [7, 3, 3] 0 4 /\
      PackedReviewerStageFCapstone [7, 3, 3] 5 7 :=
  packedReviewerStageFCapstone_invalidQueries

/-- Invalid endpoint pairs return the exact `.done none` run with an empty
trace. -/
theorem egcpStageFInvalidRunExact :
    forall (xs : List Int) (left right : Nat),
      Not (left < right /\
          right <= (SuccinctClassic.cartesianShape xs).size) ->
        (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).terminal =
              some none /\
          (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).trace = [] :=
  fun xs left right hbad =>
    packedReviewerStageFInvalidRunExact xs left right hbad

/-- The duplicate-minimum fixture: reference value, leftmost-tie spec, and
the packed run's own terminal, all at `[7, 3, 3]` with query `(0, 3)`. -/
theorem egcpStageFDuplicateMinimum :
    (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1 /\
      LeftmostArgMin [7, 3, 3] 0 3 1 /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 1) :=
  ⟨packedReviewerStageFDuplicateMinReference,
    packedReviewerStageFDuplicateMinLeftmost,
    packedReviewerStageFDuplicateMinRun⟩

/-- No second representation: the controller entry and the memory builder are
single uniform definitions with no size or readiness dispatch. -/
theorem egcpStageFNoSecondRepresentation :
    (forall n left right : Nat,
        packedReviewerController n left right =
          if left < right /\ right <= n then .header n left right
          else .done none) /\
      (forall shape : CartesianShape,
        packedReviewerMemory shape =
          (List.range (packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape))).map fun i =>
            ((packedReviewerPaddedBits shape).drop
              (i * packedReviewerCellWidth shape.size)).take
              (packedReviewerCellWidth shape.size)) :=
  ⟨packedReviewerControllerUniformEntry, packedReviewerMemoryUniformBuilder⟩

/-! ### Stage-F residual campaign: the pinned fixture (`FG-11` value liveness)

The fixture is frozen by matrix section 10.2: input `[7, 3, 3]`, query
`(0, 3)`, decisive consumed cell `8`, proved-unread allocated cell `4`.  The
expected types below restate the value-projection inequality, the complete
unread-cell run equality, and the metadata-completion bridge independently.
-/

/-- Mutating only consumed cell `8` changes the returned answer: the
inequality is at the `.terminal` projection of the two runs of the identical
driver, and both sides are proper terminal values. -/
theorem egcpStageFDecisiveCellLiveness :
    (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
          some (some 1) /\
      (packedReviewerRunAgainstMemory
          ((packedReviewerMemory
              (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
            egcpDecisiveMutantCell)
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 2) /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal ≠
        (packedReviewerRunAgainstMemory
            ((packedReviewerMemory
                (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
              egcpDecisiveMutantCell)
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal :=
  packedReviewerDecisiveCellLiveness

/--
The decisive occurrence chain, restated at its full literal expected type
(`R1`): the producing invocation fields, the driver prefix decomposition to
the pre-state, the `nextRequest`/`consumeReply` transition, and the checked
continuation to the same run's `.done (some 1)` must all survive in the
producer's conclusion.  Weakening the producer back to the rejected
origin-erasing proposition makes this consumer fail to elaborate.
-/
theorem egcpStageFDecisiveCellConnection :
    exists (position : Nat) (event : PackedReviewerPhysicalEvent)
      (request : PackedReviewerLogicalRequest) (replyCell : List Bool)
      (preState postState : PackedReviewerControllerState),
      ((packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace)[position]? =
          some event /\
      position = 11 /\
      event.request.origin = PackedReviewerPhysicalOrigin.wholeQuery request /\
      request.invocation.instruction =
        PackedReviewerInstructionSite.leftSelect /\
      request.invocation.argument = 0 /\
      request.invocation.argument2 = 0 /\
      request.site = PackedReviewerReadSite.entryFirstOffset /\
      request.segment = 8 /\
      request.index = 0 /\
      event.request.address = 8 /\
      event.reply = some replyCell /\
      event.reply =
        (packedReviewerMemory
          (SuccinctClassic.cartesianShape [7, 3, 3]))[event.request.address]? /\
      preState =
        packedReviewerDriveStateAt
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (packedReviewerController
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3)
          position /\
      packedReviewerNextRequest preState = some event.request /\
      packedReviewerConsumeReply preState event.reply = postState /\
      (packedReviewerDriveAgainstMemoryAux
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (packedReviewerControllerMeasure
              (packedReviewerController
                (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) -
            (position + 1))
          postState).terminal = some (some 1) /\
      (packedReviewerDriveAgainstMemoryAux
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (packedReviewerControllerMeasure
              (packedReviewerController
                (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) -
            (position + 1))
          postState).state = .done (some 1) /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 1) /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).state =
        .done (some 1) /\
      (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1 :=
  packedReviewerDecisiveCellConnection

/-- Mutating the proved-unread allocated cell `4` changes nothing: complete
run-record equality (terminal, failed, state, and trace), for every
replacement cell, with the allocated-cell bound recorded beside it. -/
theorem egcpStageFUnreadCellAccept :
    (4 < packedReviewerCellCount
        (SuccinctClassic.cartesianShape [7, 3, 3]).size
        (longCount (SuccinctClassic.cartesianShape [7, 3, 3]))
        (packedReviewerSparseCount
          (SuccinctClassic.cartesianShape [7, 3, 3]))) /\
      (forall event,
        event ∈ (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace ->
          event.request.address ≠ 4) /\
      (forall replacement : List Bool,
        packedReviewerRunAgainstMemory
            ((packedReviewerMemory
                (SuccinctClassic.cartesianShape [7, 3, 3])).set 4 replacement)
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 =
          packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) :=
  packedReviewerUnreadCellAccept

/-- The pinned `A02` instance at the frozen committed replacement value. -/
theorem egcpStageFUnreadCellAcceptPinned :
    packedReviewerRunAgainstMemory
        ((packedReviewerMemory
            (SuccinctClassic.cartesianShape [7, 3, 3])).set 4
          egcpStageFUnreadReplacementCell)
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 =
      packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 :=
  packedReviewerUnreadCellAcceptPinned

/-- The `M06` bridge: no completion function of the public metadata alone --
including the enacted `some n` oracle and the reference-semantics oracle of
the pinned query -- can produce both fixture terminals, with the guards and
quantifiers of the decisive-cell pair. -/
theorem egcpStageFNoMetadataCompletion :
    forall f : Nat -> Nat -> Nat -> Option Nat,
      Not ((packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
              some (f (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) /\
          (packedReviewerRunAgainstMemory
              ((packedReviewerMemory
                  (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
                egcpDecisiveMutantCell)
              (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
            some (f (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3)) :=
  packedReviewerNoMetadataCompletion

end Validation
end PackedCellProbe
end SuccinctFinal
end RMQ

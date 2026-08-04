import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceFactorization
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Payload
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Header
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Space
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Address
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe

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

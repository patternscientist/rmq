import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceFactorization

/-!
# Exact-type consumers for the EG-CP packed cell-probe candidate

Every declaration below writes out the proposition or signature it depends on in
full and then discharges it with the corresponding library result. The point is
that the expected type is stated here, independently of the current declaration in
`SourceFactorization.lean`, so weakening a library theorem breaks this file rather
than silently adapting to it.

`#print axioms` over a theorem's current type does not do this: it reports what the
declaration happens to say now. These consumers say what it must say.

This file is the validation root for the falsification gate. It presently pins the
address-factorization leaf only. The packed memory, controller, lowering,
correctness, cap and space obligations are not stated here because they do not yet
exist, and a consumer for an absent theorem would be a placeholder rather than a
check.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe
namespace Validation

open RMQ.Cartesian

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

end Validation
end PackedCellProbe
end SuccinctFinal
end RMQ

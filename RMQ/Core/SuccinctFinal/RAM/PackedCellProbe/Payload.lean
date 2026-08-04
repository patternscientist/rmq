import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceFactorization

/-!
# The raw payload the packed representation stores

This module discharges `EG-CP` falsification row `FG-01-RAW-PAYLOAD-IDENTITY`.

The packed representation stores exactly one bit string of input-dependent
content: the canonical flat RMQ payload
`concreteBPNativeSuccinctRMQPayload builtGenericSparseExceptionSelectBPCloseAccessFamily`.
`packedPayloadBits` names that object; the equalities below are `rfl`, so the
right-hand side is the existing canonical definition rather than a re-derived
copy.

This is stated separately from the payload *length* result in `Header.lean`.
A length agreement is compatible with a sibling payload of the same size; only
an identity is not.

## What this module does not establish

* Nothing here concerns cells, widths or execution. It fixes which bit string
  the later modules are allowed to chunk.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The one stored bit string -/

/--
The payload bits the packed representation stores, named at the flat layout the
rest of this development already uses.
-/
def packedPayloadBits (shape : CartesianShape) : List Bool :=
  (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload

/--
**Raw payload identity.** The bits stored by the packed representation are the
canonical flat RMQ payload object, at its existing definition site.

The proof is `rfl`: the flat layout's `payload` field *is* that application, so
there is no second payload object, no re-derived copy, and no room for a
structurally equal sibling to be substituted.
-/
theorem packedPayloadBits_eq_canonical (shape : CartesianShape) :
    packedPayloadBits shape =
      concreteBPNativeSuccinctRMQPayload
        builtGenericSparseExceptionSelectBPCloseAccessFamily shape :=
  rfl

/--
The same identity at the list-facing front door, so the object the packed
modules store is the object built from an ordinary `List Int` input.
-/
def packedPayloadBitsOfList (xs : List Int) : List Bool :=
  packedPayloadBits (Cartesian.shape xs)

theorem packedPayloadBitsOfList_eq_canonical (xs : List Int) :
    packedPayloadBitsOfList xs =
      concreteBPNativeSuccinctRMQPayload
        builtGenericSparseExceptionSelectBPCloseAccessFamily
        (Cartesian.shape xs) :=
  rfl

/--
The canonical payload is the BP code followed by the auxiliary payload, and
nothing else.

Expanding one level is what makes "no hidden table" checkable rather than
asserted: the whole stored string is these two pieces, so any additional table
would have to appear inside one of them and would be counted by the space row.
-/
theorem packedPayloadBits_eq_bpCode_append_aux (shape : CartesianShape) :
    packedPayloadBits shape =
      shape.bpCode ++
        concreteBPNativeSuccinctRMQAuxPayload
          builtGenericSparseExceptionSelectBPCloseAccessFamily shape :=
  rfl

end PackedCellProbe
end SuccinctFinal
end RMQ

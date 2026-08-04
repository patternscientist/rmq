import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Boundaries
import RMQ.Core.SuccinctRMQClassic

/-!
# The payload the accepted semantics consumes

`DD-20260804-038` decided, on the strength of the frozen registry's
`M11-SIBLING-PAYLOAD`, that `FG-01`'s `payloadBits` is the object the accepted RMQ
semantics consumes rather than the identifier the row happens to name. This module
is the first step of that re-target: it names that object and proves the identity
clause against it.

The identity is `rfl` at the existing definition site in both directions -- against
the shape-facing `concreteBPNativeSuccinctRMQCanonicalReviewerPayload` and against
the `List Int`-facing `buildPayload`, which is what the public
`listInt_two_n_plus_o_constant_query_profile` and the strengthened execution story
are stated about.

Nothing here re-derives a payload. `packedReviewerPayloadBits` is a name for an
existing object, which is what `FG-01`'s evidence clause demands and what
`M11-SIBLING-PAYLOAD` exists to check.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian

/-- The payload the accepted RMQ semantics consumes, named at the packed layer. -/
def packedReviewerPayloadBits (shape : CartesianShape) : List Bool :=
  concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape

/-- **The identity, shape-facing.** -/
theorem packedReviewerPayloadBits_eq_canonical (shape : CartesianShape) :
    packedReviewerPayloadBits shape =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape :=
  rfl

/--
**The identity, at the object the public claim is stated about.** `buildPayload`
is the advertised `2 * n + o(n)` payload of
`listInt_two_n_plus_o_constant_query_profile`.
-/
theorem packedReviewerPayloadBits_eq_buildPayload (xs : List Int) :
    packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs) =
      SuccinctClassic.buildPayload xs :=
  rfl

/-- The space clause, over the same object. -/
theorem packedReviewerPayloadBits_length_le
    {n : Nat} {shape : CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (packedReviewerPayloadBits shape).length <=
      2 * n + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n :=
  concreteBPNativeSuccinctRMQCanonicalReviewerPayload_length_le hshape

/-- Its residual is little-o linear, so the re-target preserves `FG-06`'s shape. -/
theorem packedReviewerOverhead_littleO :
    SuccinctSpace.LittleOLinear
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead :=
  concreteBPNativeSuccinctRMQCanonicalReviewerOverhead_littleO

/--
**The executed store reads this object.** Segment `20` is its close component,
`21` and `22` its two chunk tables -- exactly the three the flat payload lacked
(`DD-20260804-027`). Re-targeting therefore removes that deficit rather than
relocating it.
-/
theorem packedReviewerPayload_backs_executedCloseSegments
    (shape : CartesianShape) (index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 index =
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words[index]? /\
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 index =
        (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits
            shape.bpCode.length)).store.words[index]? /\
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 index =
        (SuccinctClose.bpChunkSelectTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
          false).store.words[index]? :=
  ⟨packedExecutedStore_interiorComponentSegment shape index,
    packedExecutedStore_fringeChunkSegment shape index,
    packedExecutedStore_selectChunkSegment shape index⟩

end PackedCellProbe

end SuccinctFinal

end RMQ

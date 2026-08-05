import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerMemory

/-!
# Round trip and cell crossing over the consumed payload

The rest of step three of the `DD-20260804-038` re-target: the `FG-05` chunking
round trip, and the two-cell bound on an unaligned span, both over
`packedReviewerMemory`.

`packedReviewerMemory_flatten` says the cell array and the padded bit string are
two views of one object -- nothing is lost and nothing is invented.
`packedReviewerMemory_recovers_payload` then says every bit of the consumed
payload is inside those cells, so no part of it lives anywhere else.

`packedReviewerSpan_from_two_cells` is the clause that bounds the physical probe
count: any span no wider than one cell, at any bit position aligned or not, is a
slice of **two** consecutive cells. When the span is aligned, or short enough to
sit inside one cell, the second cell contributes nothing -- so this covers the
non-crossing case rather than assuming a crossing occurs.

## What this module does not establish

* Nothing here issues a probe. This bounds what a probe plan *could* need; that a
  controller issues exactly these cells is the `FG-08` lowering obligation.
* The two-cell bound is stated over `packedReviewerPaddedBits`. Connecting it to a
  source's logical word needs the per-source geometries, which are still stated
  over the flat payload.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The round trip -/

/--
Chunking a bit string of exactly `k * w` bits into `k` width-`w` cells, then
concatenating them, recovers it. A copy of `Memory.lean`'s lemma, which is
`private` there; it is a general list fact with no payload content.
-/
private theorem packedReviewerChunkFlatten (w : Nat) :
    forall (k : Nat) (bs : List Bool), bs.length = k * w ->
      ((List.range k).map fun i => (bs.drop (i * w)).take w).flatten = bs := by
  intro k
  induction k with
  | zero =>
      intro bs hbs
      simp only [Nat.zero_mul] at hbs
      simp [List.eq_nil_of_length_eq_zero hbs]
  | succ k ih =>
      intro bs hbs
      have hdrop : (bs.drop w).length = k * w := by
        rw [List.length_drop, hbs, Nat.succ_mul]
        omega
      have htail :
          ((List.range k).map fun i => (bs.drop ((i + 1) * w)).take w) =
            ((List.range k).map fun i => ((bs.drop w).drop (i * w)).take w) := by
        apply List.map_congr_left
        intro i _
        rw [List.drop_drop, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.flatten_cons, Function.comp_def,
        Nat.zero_mul, List.drop_zero]
      rw [htail, ih (bs.drop w) hdrop, List.take_append_drop]

theorem packedReviewerMemory_flatten
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (packedReviewerMemory shape).flatten = packedReviewerPaddedBits shape := by
  refine packedReviewerChunkFlatten (packedReviewerCellWidth shape.size)
    (packedReviewerCellCount shape.size (longCount shape))
    (packedReviewerPaddedBits shape) ?_
  rw [packedReviewerPaddedBits_length shape hstride]
  rfl

theorem packedReviewerMemory_flatten_take
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    (packedReviewerMemory shape).flatten.take
        (packedReviewerSerializedBits shape).length =
      packedReviewerSerializedBits shape := by
  rw [packedReviewerMemory_flatten shape hstride]
  unfold packedReviewerPaddedBits
  simp

/-! ### Cell crossing -/

def packedReviewerCellAt (shape : CartesianShape) (i : Nat) : List Bool :=
  ((packedReviewerPaddedBits shape).drop
    (i * packedReviewerCellWidth shape.size)).take
    (packedReviewerCellWidth shape.size)

theorem packedReviewerMemory_getElem?
    (shape : CartesianShape) {i : Nat}
    (hi : i < packedReviewerCellCount shape.size (longCount shape)) :
    (packedReviewerMemory shape)[i]? = some (packedReviewerCellAt shape i) := by
  unfold packedReviewerMemory packedReviewerCellAt
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

theorem packedReviewerCellPair (shape : CartesianShape) (i : Nat) :
    packedReviewerCellAt shape i ++ packedReviewerCellAt shape (i + 1) =
      ((packedReviewerPaddedBits shape).drop
        (i * packedReviewerCellWidth shape.size)).take
        (packedReviewerCellWidth shape.size +
          packedReviewerCellWidth shape.size) := by
  unfold packedReviewerCellAt
  rw [List.take_add]
  congr 1
  rw [List.drop_drop]
  congr 1
  rw [Nat.add_mul, Nat.one_mul]

theorem packedReviewerSpan_from_two_cells
    (shape : CartesianShape) (p width : Nat)
    (hwidth : width <= packedReviewerCellWidth shape.size) :
    ((packedReviewerPaddedBits shape).drop p).take width =
      ((packedReviewerCellAt shape (p / packedReviewerCellWidth shape.size) ++
          packedReviewerCellAt shape
            (p / packedReviewerCellWidth shape.size + 1)).drop
            (p % packedReviewerCellWidth shape.size)).take width := by
  have hw : 0 < packedReviewerCellWidth shape.size :=
    packedReviewerCellWidth_pos shape.size
  have hmod :
      p % packedReviewerCellWidth shape.size <
        packedReviewerCellWidth shape.size :=
    Nat.mod_lt _ hw
  have hidx :
      p / packedReviewerCellWidth shape.size *
            packedReviewerCellWidth shape.size +
          p % packedReviewerCellWidth shape.size = p := by
    have h1 := Nat.mod_add_div p (packedReviewerCellWidth shape.size)
    have h2 :
        packedReviewerCellWidth shape.size *
            (p / packedReviewerCellWidth shape.size) =
          p / packedReviewerCellWidth shape.size *
            packedReviewerCellWidth shape.size :=
      Nat.mul_comm _ _
    omega
  have hmin :
      min width
          (packedReviewerCellWidth shape.size +
            packedReviewerCellWidth shape.size -
            p % packedReviewerCellWidth shape.size) = width := by
    omega
  rw [packedReviewerCellPair, List.drop_take, List.take_take, List.drop_drop,
    hidx, hmin]

/-! ### The payload is recoverable from the cells alone -/

/--
**Every bit of the consumed payload is in the cells.** Dropping the header cell
from the flattened memory and taking the payload's own length returns the payload
itself, so no part of it lives outside `packedReviewerMemory`.
-/
theorem packedReviewerMemory_recovers_payload
    (shape : CartesianShape)
    (hstride : GenericSelect.localStride shape.bpCode.length = 1) :
    ((packedReviewerMemory shape).flatten.drop
          (packedReviewerCellWidth shape.size)).take
        (packedReviewerPayloadBits shape).length =
      packedReviewerPayloadBits shape := by
  rw [packedReviewerMemory_flatten shape hstride]
  unfold packedReviewerPaddedBits packedReviewerSerializedBits
  rw [List.append_assoc, ← packedReviewerHeaderBits_length shape,
    List.drop_left]
  simp

end PackedCellProbe
end SuccinctFinal
end RMQ

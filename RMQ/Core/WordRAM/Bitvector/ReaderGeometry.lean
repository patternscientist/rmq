import RMQ.Core.WordRAM.Bitvector.WordBounds
import RMQ.Core.WordRAM.Packed.LogicalSpan

/-! # Decode exact canonical component words from their counted bit spans -/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect Experiment
open SuccinctFinal.PackedWordRAM

/-- Exact recovery from an arbitrary dense serialization of regular components.
The zero-length branch permits nominal sentinel positions beyond the body. -/
theorem decode_serialized_view (headers : List Nat) (physicalWidth : Nat)
    (segments : List (Array (List Bool))) (component index : Nat)
    (hc : component < segments.length)
    (words : Array (List Bool)) (herase : segmentBits words = segmentBits segments[component])
    (hi : index < words.size)
    (hp : 0 < physicalWidth) (hr : RegularWords words)
    (hw : firstLength words ≤ physicalWidth) :
    let stride := firstLength words
    let len := min stride ((segmentBits words).length - index * stride)
    decodeSpanNat physicalWidth
      (headers.length * physicalWidth + componentOffset segments component + index * stride)
      len (headers ++ denseWords physicalWidth (segments.flatMap segmentBits)) =
        some (bitsToNatLE words[index]) := by
  let stride := firstLength words
  let len := min stride ((segmentBits words).length - index * stride)
  have hwidth : len ≤ physicalWidth := by
    exact Nat.le_trans (Nat.min_le_left _ _) hw
  have hlocal : index * stride + len ≤ (segmentBits words).length ∨ len = 0 := by
    by_cases hz : len = 0
    · exact Or.inr hz
    · left
      have hmin := Nat.min_le_right stride ((segmentBits words).length - index * stride)
      omega
  have hcomponent : index * stride + len ≤ (segmentBits segments[component]).length ∨ len = 0 := by
    rw [← herase]
    exact hlocal
  have hbound := component_span_bound segments component (index * stride) len hc hcomponent
  have hd := decodeSpanNat_repacked_span headers physicalWidth [segments.flatMap segmentBits]
    (componentOffset segments component + index * stride) len hp hwidth
    (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hbound)
  have hs := component_slice segments component (index * stride) len hc hcomponent
  rw [← herase] at hs
  have hword := hr.min_slice_eq index hi
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, repackWords,
    ← Nat.add_assoc] at hd
  change decodeSpanNat _ _ len _ = _
  rw [hd]
  congr 1
  congr 1
  exact (show ((segments.flatMap segmentBits).drop
    (componentOffset segments component + index * stride)).take len = words[index] from
      hs.trans hword.symm)

/-- In particular, every present word in the serialized component is recovered. -/
theorem decode_serialized_word (headers : List Nat) (physicalWidth : Nat)
    (segments : List (Array (List Bool))) (component index : Nat)
    (hc : component < segments.length)
    (hi : index < segments[component].size)
    (hp : 0 < physicalWidth) (hr : RegularWords segments[component])
    (hw : firstLength segments[component] ≤ physicalWidth) :
    let words := segments[component]
    let stride := firstLength words
    let len := min stride ((segmentBits words).length - index * stride)
    decodeSpanNat physicalWidth
      (headers.length * physicalWidth + componentOffset segments component + index * stride)
      len (headers ++ denseWords physicalWidth (segments.flatMap segmentBits)) =
        some (bitsToNatLE words[index]) :=
  decode_serialized_view headers physicalWidth segments component index hc
    segments[component] rfl hi hp hr hw

/-- The generic decoder theorem specializes to exactly the route experiment's
memory, with regularity and word-width hypotheses derived from its builders. -/
theorem decode_component_word (bits : List Bool) (component index : Nat)
    (hc : component < 35)
    (hi : index < ((allSegments bits)[component]'(by simpa using hc)).size) :
    let words := (allSegments bits)[component]'(by simpa using hc)
    let stride := firstLength words
    let len := min stride ((segmentBits words).length - index * stride)
    decodeSpanNat (width bits.length)
      (207 * width bits.length + componentOffset (allSegments bits) component + index * stride)
      len (memory bits) = some (bitsToNatLE words[index]) := by
  have hcomp : component < (allSegments bits).length := by simpa using hc
  have hm : (allSegments bits)[component] ∈ allSegments bits := List.getElem_mem hcomp
  have h := decode_serialized_word (header bits) (width bits.length)
    (allSegments bits) component index hcomp hi (width_pos bits.length)
    (allSegments_regular bits _ hm)
    (Nat.le_of_lt (allSegments_firstLength_lt bits _ hm))
  simpa only [header_length, ← memory_eq, body] using h

end RMQ.PackedBitvector

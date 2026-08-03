import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part C: the two content-dependent select components, their EXACT
length formulas, and whether the `n`-only overheads are PROVED upper bounds or
merely budgets.  Plus the flag-rank auxiliary payloads.
-/

namespace SdkC

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

/-! ## 1. Exact length formulas (repo theorems, restated verbatim) -/

#check @RMQ.GenericSelect.longSuperRelativeTable_payload_length
#check @RMQ.GenericSelect.sparseExceptionRelativeTable_payload_expanded_length

/-! ## 2. The `n`-only overheads and the bounds against them -/

#check @RMQ.GenericSelect.longSuperRelativeTableOverhead
#check @RMQ.GenericSelect.longSuperRelativeTable_payload_le_overhead
#check @RMQ.GenericSelect.sparseExceptionRelativeTableOverhead
#check @RMQ.GenericSelect.sparseExceptionRelativeTable_payload_le_overhead

/-- The long-super relative table is bounded by an `n`-only quantity for EVERY
bit list and EVERY target -- unconditionally, no hypothesis. -/
theorem long_bound_unconditional (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length <=
      longSuperRelativeTableOverhead bits.length :=
  longSuperRelativeTable_payload_le_overhead bits target

/-- Same for the sparse-exception relative table. -/
theorem sparse_bound_unconditional (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeTable bits target).payload.length <=
      sparseExceptionRelativeTableOverhead bits.length :=
  sparseExceptionRelativeTable_payload_le_overhead bits target

/-- Specialised to the live BP route: both bounds are `size`-only. -/
theorem both_bounds_at_bp (s : CartesianShape) (b : Bool) :
    (longSuperRelativeTable s.bpCode b).payload.length <=
        longSuperRelativeTableOverhead (2 * s.size) /\
      (sparseExceptionRelativeTable s.bpCode b).payload.length <=
        sparseExceptionRelativeTableOverhead (2 * s.size) := by
  have hlen : s.bpCode.length = 2 * s.size := CartesianShape.bpCode_length s
  constructor
  · have := longSuperRelativeTable_payload_le_overhead s.bpCode b
    rwa [hlen] at this
  · have := sparseExceptionRelativeTable_payload_le_overhead s.bpCode b
    rwa [hlen] at this

/-! ## 3. The overheads are closed arithmetic in `n` (evaluate them) -/

#eval (List.range 6).map (fun k =>
  let n := 2 ^ (k + 8)
  (n, longSuperRelativeTableOverhead n, sparseExceptionRelativeTableOverhead n))

/-! ## 4. Flag-rank auxiliary payloads: size-only or not? -/

theorem occ_any (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.size := by
  cases b
  · exact SuccinctSpace.bpCode_rankFalse_full s
  · exact SuccinctClose.bpCode_rankTrue_full s

theorem flagrank_params_size_only {s t : CartesianShape} (h : s.size = t.size)
    (b : Bool) :
    longFlagRankSuperOverhead s.bpCode b = longFlagRankSuperOverhead t.bpCode b /\
      longFlagRankBlockOverhead s.bpCode b =
        longFlagRankBlockOverhead t.bpCode b /\
      sparseExceptionEffectiveFlagRankSuperOverhead s.bpCode b =
        sparseExceptionEffectiveFlagRankSuperOverhead t.bpCode b /\
      sparseExceptionEffectiveFlagRankBlockOverhead s.bpCode b =
        sparseExceptionEffectiveFlagRankBlockOverhead t.bpCode b := by
  have hlen : s.bpCode.length = t.bpCode.length := by
    rw [CartesianShape.bpCode_length s, CartesianShape.bpCode_length t, h]
  have hocc : occurrenceCount s.bpCode b = occurrenceCount t.bpCode b := by
    rw [occ_any s b, occ_any t b, h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [longFlagRankSuperOverhead, longFlagRankBlockOverhead,
      sparseExceptionEffectiveFlagRankSuperOverhead,
      sparseExceptionEffectiveFlagRankBlockOverhead,
      longFlagRankWordSize, longFlagRankBlocksPerSuper,
      sparseExceptionEffectiveFlagRankWordSize,
      sparseExceptionEffectiveFlagRankBlocksPerSuper,
      longSuperFlagBits, sparseExceptionEffectiveFlagBits,
      sparseExceptionEffectiveLocalSlotCount,
      localSlotCount, superSlotCount, hlen, hocc]

end SdkC

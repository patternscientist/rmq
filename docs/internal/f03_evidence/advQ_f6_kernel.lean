import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL: kernel-check the TWO facts the whole S verdict for F6 rests on,
namely that the only two channels through which `bits` can reach the leaf body
(`bits.length` and `occurrenceCount bits target`) are both functions of
`shape.size`.  If either fails, S collapses.
-/

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

namespace AdvQF6K

/-- Channel 1: length. -/
theorem chan_length (s : CartesianShape) : s.bpCode.length = 2 * s.size :=
  CartesianShape.bpCode_length s

/-- Channel 2: the select-domain guard at ChargedRankSelectLeafTrace.lean:1168,
`if idx < occurrenceCount bits target`, with the call site's `target = false`. -/
theorem chan_occ (s : CartesianShape) :
    occurrenceCount s.bpCode false = s.size := by
  unfold occurrenceCount
  exact SuccinctSpace.bpCode_rankFalse_full s

/-- Consequently every size-derived parameter of the leaf is a function of
`s.size` alone. -/
theorem params_size_only (s : CartesianShape) :
    wordBits s.bpCode.length = wordBits (2 * s.size) /\
    superStride s.bpCode.length = superStride (2 * s.size) /\
    localStride s.bpCode.length = localStride (2 * s.size) /\
    localSlotsPerSuper s.bpCode.length = localSlotsPerSuper (2 * s.size) /\
    SuccinctClose.bpFringeChunkBits s.bpCode.length
      = SuccinctClose.bpFringeChunkBits (2 * s.size) /\
    superSlotCount s.bpCode false
      = selectCeilDiv s.size (superStride (2 * s.size)) /\
    localSlotCount s.bpCode false
      = selectCeilDiv s.size (superStride (2 * s.size))
          * localSlotsPerSuper (2 * s.size) /\
    sparseExceptionEffectiveLocalSlotCount s.bpCode false
      = Nat.min (selectCeilDiv s.size (superStride (2 * s.size))
          * localSlotsPerSuper (2 * s.size)) s.size := by
  have hl := chan_length s
  have ho := chan_occ s
  refine ⟨by rw [hl], by rw [hl], by rw [hl], by rw [hl], by rw [hl], ?_, ?_, ?_⟩
  · unfold superSlotCount; rw [hl, ho]
  · unfold localSlotCount superSlotCount; rw [hl, ho]
  · unfold sparseExceptionEffectiveLocalSlotCount localSlotCount superSlotCount
    rw [hl, ho]

/-- Corollary: two shapes of equal size agree on every one of those parameters.
This is the quantified form the defender only sampled. -/
theorem params_agree_of_size_eq (s t : CartesianShape) (h : s.size = t.size) :
    s.bpCode.length = t.bpCode.length /\
    occurrenceCount s.bpCode false = occurrenceCount t.bpCode false /\
    superSlotCount s.bpCode false = superSlotCount t.bpCode false /\
    localSlotCount s.bpCode false = localSlotCount t.bpCode false /\
    sparseExceptionEffectiveLocalSlotCount s.bpCode false
      = sparseExceptionEffectiveLocalSlotCount t.bpCode false /\
    (longSuperFlagBits s.bpCode false).length
      = (longSuperFlagBits t.bpCode false).length /\
    (sparseExceptionEffectiveFlagBits s.bpCode false).length
      = (sparseExceptionEffectiveFlagBits t.bpCode false).length := by
  have hl : s.bpCode.length = t.bpCode.length := by
    rw [chan_length s, chan_length t, h]
  have ho : occurrenceCount s.bpCode false = occurrenceCount t.bpCode false := by
    rw [chan_occ s, chan_occ t, h]
  have hsuper : superSlotCount s.bpCode false = superSlotCount t.bpCode false := by
    unfold superSlotCount; rw [hl, ho]
  have hlocal : localSlotCount s.bpCode false = localSlotCount t.bpCode false := by
    unfold localSlotCount; rw [hsuper, hl]
  refine ⟨hl, ho, hsuper, hlocal, ?_, ?_, ?_⟩
  · unfold sparseExceptionEffectiveLocalSlotCount; rw [hlocal, ho]
  · unfold longSuperFlagBits; simp [hsuper]
  · unfold sparseExceptionEffectiveFlagBits
    simp [sparseExceptionEffectiveLocalSlotCount, hlocal, ho]

/-- And therefore the two rank towers the leaf actually projects have equal
word sizes -- the divisors used at SuccinctRank.lean:813-844. -/
theorem rank_divisors_agree (s t : CartesianShape) (h : s.size = t.size) :
    longFlagRankWordSize s.bpCode false = longFlagRankWordSize t.bpCode false /\
    sparseExceptionEffectiveFlagRankWordSize s.bpCode false
      = sparseExceptionEffectiveFlagRankWordSize t.bpCode false /\
    longFlagRankBlocksPerSuper s.bpCode false
      = longFlagRankBlocksPerSuper t.bpCode false /\
    sparseExceptionEffectiveFlagRankBlocksPerSuper s.bpCode false
      = sparseExceptionEffectiveFlagRankBlocksPerSuper t.bpCode false := by
  obtain ⟨_, _, _, _, _, hlong, hsparse⟩ := params_agree_of_size_eq s t h
  refine ⟨?_, ?_, rfl, rfl⟩
  · unfold longFlagRankWordSize; rw [hlong]
  · unfold sparseExceptionEffectiveFlagRankWordSize; rw [hsparse]

end AdvQF6K

#print axioms AdvQF6K.chan_length
#print axioms AdvQF6K.chan_occ
#print axioms AdvQF6K.params_agree_of_size_eq
#print axioms AdvQF6K.rank_divisors_agree

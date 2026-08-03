import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01: SELECT-DIRECTORY HEADER QUESTION, part B.

Claim under test: every scalar the live select machinery consumes is a function
of the bit length `n` alone (directly, or via the popcount which balancedness
pins to `n / 2`), EXCEPT the two relative-table lengths.

Test form: two shapes of equal `size` must agree on the scalar.  Equal `size`
gives equal `bpCode.length` and (by the popcount theorems) equal
`occurrenceCount` at BOTH targets; nothing else about the content is shared.
-/

namespace SdkB

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

theorem occ_any (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.size := by
  cases b
  · exact SuccinctSpace.bpCode_rankFalse_full s
  · exact SuccinctClose.bpCode_rankTrue_full s

theorem len_eq {s t : CartesianShape} (h : s.size = t.size) :
    s.bpCode.length = t.bpCode.length := by
  rw [CartesianShape.bpCode_length s, CartesianShape.bpCode_length t, h]

theorem occ_eq {s t : CartesianShape} (h : s.size = t.size) (b : Bool) :
    occurrenceCount s.bpCode b = occurrenceCount t.bpCode b := by
  rw [occ_any s b, occ_any t b, h]

/-! ## The pure `n`-only parameter layer (no popcount even needed) -/

theorem params_size_only {s t : CartesianShape} (h : s.size = t.size) :
    wordBits s.bpCode.length = wordBits t.bpCode.length /\
      ell s.bpCode.length = ell t.bpCode.length /\
      superStride s.bpCode.length = superStride t.bpCode.length /\
      localStride s.bpCode.length = localStride t.bpCode.length /\
      superLongSpan s.bpCode.length = superLongSpan t.bpCode.length /\
      localSparseSpan s.bpCode.length = localSparseSpan t.bpCode.length /\
      localSlotsPerSuper s.bpCode.length = localSlotsPerSuper t.bpCode.length /\
      superFieldWidth s.bpCode = superFieldWidth t.bpCode /\
      localFieldWidth s.bpCode = localFieldWidth t.bpCode /\
      longSuperRelativeWidth s.bpCode = longSuperRelativeWidth t.bpCode /\
      sparseExceptionRelativeWidth s.bpCode =
        sparseExceptionRelativeWidth t.bpCode := by
  have hlen := len_eq h
  refine ⟨by rw [hlen], by rw [hlen], by rw [hlen], by rw [hlen], by rw [hlen],
    by rw [hlen], by rw [hlen], ?_, ?_, ?_, ?_⟩
  · simp [superFieldWidth, wordBits, hlen]
  · simp [localFieldWidth, sparseExceptionRelativeWidth, hlen]
  · simp [longSuperRelativeWidth, hlen]
  · simp [sparseExceptionRelativeWidth, hlen]

/-! ## The slot-count layer: forced by the popcount, hence by `n` -/

theorem slot_counts_size_only {s t : CartesianShape} (h : s.size = t.size)
    (b : Bool) :
    superSlotCount s.bpCode b = superSlotCount t.bpCode b /\
      localSlotCount s.bpCode b = localSlotCount t.bpCode b /\
      sparseExceptionEffectiveLocalSlotCount s.bpCode b =
        sparseExceptionEffectiveLocalSlotCount t.bpCode b := by
  have hlen := len_eq h
  have hocc := occ_eq h b
  refine ⟨?_, ?_, ?_⟩
  · simp [superSlotCount, hlen, hocc]
  · simp [localSlotCount, superSlotCount, hlen, hocc]
  · simp [sparseExceptionEffectiveLocalSlotCount, localSlotCount,
      superSlotCount, hlen, hocc]

/-! ## Entry-list lengths and flag-vector lengths: forced -/

theorem list_lengths_size_only {s t : CartesianShape} (h : s.size = t.size)
    (b : Bool) :
    (superEntries s.bpCode b).length = (superEntries t.bpCode b).length /\
      (localEntries s.bpCode b).length = (localEntries t.bpCode b).length /\
      (longSuperFlagBits s.bpCode b).length =
        (longSuperFlagBits t.bpCode b).length /\
      (sparseExceptionEffectiveFlagBits s.bpCode b).length =
        (sparseExceptionEffectiveFlagBits t.bpCode b).length := by
  obtain ⟨hsuper, hlocal, hsparse⟩ := slot_counts_size_only h b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [superEntries_length, superEntries_length, hsuper]
  · rw [localEntries_length, localEntries_length, hlocal]
  · simp [longSuperFlagBits, hsuper]
  · rw [sparseExceptionEffectiveFlagBits_length,
      sparseExceptionEffectiveFlagBits_length, hsparse]

/-! ## Dense table payload lengths: forced (count x fixed width) -/

theorem dense_table_lengths_size_only {s t : CartesianShape}
    (h : s.size = t.size) (b : Bool) :
    (superTable s.bpCode b).payload.length =
        (superTable t.bpCode b).payload.length /\
      (localTable s.bpCode b).payload.length =
        (localTable t.bpCode b).payload.length := by
  obtain ⟨hse, hle, _, _⟩ := list_lengths_size_only h b
  obtain ⟨_, _, _, _, _, _, _, hsw, hlw, _, _⟩ := params_size_only h
  constructor
  · rw [(superTable s.bpCode b).payload_length,
      (superTable t.bpCode b).payload_length]
    simp [sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget, hse, hsw]
  · rw [(localTable s.bpCode b).payload_length,
      (localTable t.bpCode b).payload_length]
    simp [sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget, hle, hlw]

end SdkB

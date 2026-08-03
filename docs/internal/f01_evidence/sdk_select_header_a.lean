import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01 sub-question: does the SELECT directory need any header field?

Part A: the popcount facts, and the "size-only" classification of every
scalar the live generic select machinery consumes.
-/

namespace SdkA

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

/-! ## 1. The two popcount facts, verbatim -/

#check @RMQ.SuccinctSpace.bpCode_rankFalse_full
#check @RMQ.SuccinctClose.bpCode_rankTrue_full
#check @RMQ.SuccinctSelect.falseSelectOccurrenceCount_eq_size

/-- The LIVE generic-layer occurrence count for `target = false`, all shapes. -/
theorem occ_false (s : CartesianShape) :
    occurrenceCount s.bpCode false = s.size :=
  SuccinctSpace.bpCode_rankFalse_full s

/-- The `true` counterpart, all shapes. -/
theorem occ_true (s : CartesianShape) :
    occurrenceCount s.bpCode true = s.size :=
  SuccinctClose.bpCode_rankTrue_full s

/-- BOTH targets, uniformly: the select domain size is `size`, i.e. `n / 2`
where `n = bpCode.length`.  No content is read. -/
theorem occ_any (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.size := by
  cases b
  · exact occ_false s
  · exact occ_true s

theorem bp_len (s : CartesianShape) : s.bpCode.length = 2 * s.size :=
  CartesianShape.bpCode_length s

/-- The select domain size is a closed function of the bit length alone. -/
theorem occ_of_length (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.bpCode.length / 2 := by
  rw [occ_any s b, bp_len s]
  omega

end SdkA

import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part F: consolidation, executed crossover check, axiom audit.
-/

namespace SdkF

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

/-! ## The verdict theorem -/

theorem occ_any (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.size := by
  cases b
  · exact SuccinctSpace.bpCode_rankFalse_full s
  · exact SuccinctClose.bpCode_rankTrue_full s

/--
SELECT DIRECTORY NEEDS NO HEADER FIELD FOR ITS DOMAIN SIZE.

For every shape and BOTH targets, the select domain size (the popcount that a
general bitvector would have to store) equals `size`, which is `bpCode.length / 2`.
Consequently every stride, span threshold, field width, slot count, entry-list
length and flag-vector length is a closed function of the bit length.
-/
theorem select_domain_size_is_free (s : CartesianShape) (b : Bool) :
    occurrenceCount s.bpCode b = s.bpCode.length / 2 := by
  rw [occ_any s b, CartesianShape.bpCode_length s]
  omega

/--
K = 1 IS ACHIEVABLE: the only two select components whose length is not a
closed function of `n` both admit an UNCONDITIONAL, `o(n)` upper bound that is a
closed function of `n`.  Padding each region to its budget makes every base
offset `n`-derived without exceeding an `o(n)` overhead.
-/
theorem both_relative_tables_fit_n_only_budgets
    (bits : List Bool) (target : Bool) :
    (longSuperRelativeTable bits target).payload.length <=
        longSuperRelativeTableOverhead bits.length /\
      (sparseExceptionRelativeTable bits target).payload.length <=
        sparseExceptionRelativeTableOverhead bits.length /\
      SuccinctSpace.LittleOLinear longSuperRelativeTableOverhead /\
      SuccinctSpace.LittleOLinear sparseExceptionRelativeTableOverhead :=
  ⟨longSuperRelativeTable_payload_le_overhead bits target,
    sparseExceptionRelativeTable_payload_le_overhead bits target,
    longSuperRelativeTableOverhead_littleO,
    sparseExceptionRelativeTableOverhead_littleO⟩

/-! ## Executed crossover check for `superIsLong`

`superIsLong` compares a super span against `superLongSpan n = w^2 * w * ell`.
A super span cannot exceed `n`, so no super can be long while
`superLongSpan n >= n`.  Scan the crossover directly. -/

#eval
  let rows := (List.range 26).map (fun k =>
    let n := 2 ^ k
    (k, n, superLongSpan n, decide (n <= superLongSpan n)))
  rows.filter (fun r => r.2.2.2 = false)

/-! ## Axiom audit -/

#print axioms occ_any
#print axioms select_domain_size_is_free
#print axioms both_relative_tables_fit_n_only_budgets
#print axioms RMQ.SuccinctSpace.bpCode_rankFalse_full
#print axioms RMQ.SuccinctClose.bpCode_rankTrue_full
#print axioms RMQ.SuccinctSelect.falseSelectOccurrenceCount_eq_size
#print axioms RMQ.GenericSelect.longSuperRelativeTable_payload_le_overhead
#print axioms RMQ.GenericSelect.sparseExceptionRelativeTable_payload_le_overhead
#print axioms RMQ.GenericSelect.longSuperRelativeTable_payload_length
#print axioms
  RMQ.GenericSelect.sparseExceptionRelativeTable_payload_expanded_length

end SdkF

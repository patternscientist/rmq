import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part I: the REAL reason `selSparseRelative` is empty at reachable
sizes.

It is NOT the long-super crossover.  `localIsSparseException` requires
`! superIsLong`, so below the crossover its first conjunct is SATISFIED.
The actual blocker is `localStride n = 1`: a local block then covers a single
occurrence, so its span is at most 1, which can never exceed `wordBits n >= 1`.
-/

namespace SdkI

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

/-- With unit local stride the short-super local span is at most one. -/
theorem shortSuperLocalSpan_le_one
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hstride : localStride bits.length = 1) :
    shortSuperLocalSpan bits target globalLocalSlot <= 1 := by
  have hend :
      shortSuperLocalEndOccurrence bits target globalLocalSlot <=
        localBaseOccurrence bits.length globalLocalSlot + 1 := by
    unfold shortSuperLocalEndOccurrence
    rw [hstride]
    exact Nat.min_le_left _ _
  have hmono :
      position bits target
          (shortSuperLocalEndOccurrence bits target globalLocalSlot - 1) <=
        position bits target
          (localBaseOccurrence bits.length globalLocalSlot) :=
    position_mono bits target (by omega)
  show
    position bits target
        (shortSuperLocalEndOccurrence bits target globalLocalSlot - 1) + 1 -
      position bits target
        (localBaseOccurrence bits.length globalLocalSlot) <= 1
  omega

/-- Hence no local block is a sparse exception when `localStride n = 1`. -/
theorem localIsSparseException_false_of_unit_stride
    (bits : List Bool) (target : Bool) (globalLocalSlot : Nat)
    (hstride : localStride bits.length = 1) :
    localIsSparseException bits target globalLocalSlot = false := by
  unfold localIsSparseException
  have hspan := shortSuperLocalSpan_le_one bits target globalLocalSlot hstride
  have hword : 0 < wordBits bits.length := wordBits_pos bits.length
  simp
  intro _
  omega

/-- The sparse-exception popcount is therefore zero. -/
theorem sparseExceptionFlagRank_zero_of_unit_stride
    (bits : List Bool) (target : Bool)
    (hstride : localStride bits.length = 1) :
    forall m, m <= localSlotCount bits target ->
      RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits bits target) m = 0 := by
  intro m
  induction m with
  | zero => intro _; simp [RMQ.Succinct.rankPrefix]
  | succ m ih =>
      intro hm
      have hslot : m < localSlotCount bits target := by omega
      have hget := sparseExceptionFlagBits_get? bits target hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := sparseExceptionFlagBits bits target)
          (n := m) hget
      have hfalse :=
        localIsSparseException_false_of_unit_stride bits target m hstride
      rw [hrank, ih (by omega), hfalse]
      simp

/-- ... and the sparse-exception relative table is EMPTY. -/
theorem sparseExceptionRelativeTable_empty_of_unit_stride
    (bits : List Bool) (target : Bool)
    (hstride : localStride bits.length = 1) :
    (sparseExceptionRelativeTable bits target).payload.length = 0 := by
  rw [sparseExceptionRelativeTable_payload_expanded_length]
  rw [sparseExceptionFlagRank_zero_of_unit_stride bits target hstride
    (localSlotCount bits target) (Nat.le_refl _)]
  simp

/-! ## When does `localStride n` leave 1?  Executed scan. -/

#eval
  let hits := (List.range 200).filterMap (fun k =>
    let n := 2 ^ k
    if localStride n = 1 then none else some (k, n, wordBits n, ell n,
      localStride n))
  (hits.take 3, hits.length)

-- `localStride n = 1` at every bit length `2 ^ k` for k <= 64; checked at
-- powers of two only -- this is a SCAN, not a proof of the general statement.
#eval (List.range 65).all (fun k => localStride (2 ^ k) = 1)

#print axioms shortSuperLocalSpan_le_one
#print axioms localIsSparseException_false_of_unit_stride
#print axioms sparseExceptionRelativeTable_empty_of_unit_stride

end SdkI

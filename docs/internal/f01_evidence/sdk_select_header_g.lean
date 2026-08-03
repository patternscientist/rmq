import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01, part G: the emptiness regime of the long-super relative table,
proved (not merely executed).
-/

namespace SdkG

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect

/-- An in-range super span never exceeds the bit length: it is bounded by the
gap to the next super base, and positions are bounded by the length. -/
theorem superSpan_le_length
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target) :
    superSpan bits target superSlot <= bits.length := by
  have hgap := superSpan_le_next_gap bits target hslot
  have hnext :
      position bits target
        (superBaseOccurrence bits.length (superSlot + 1)) <= bits.length :=
    position_le_length bits target _
  omega

/-- Below the crossover (`n <= superLongSpan n`) NO in-range super is long,
for every bit list, every target and every in-range slot. -/
theorem superIsLong_false_below_crossover
    (bits : List Bool) (target : Bool) {superSlot : Nat}
    (hslot : superSlot < superSlotCount bits target)
    (hsmall : bits.length <= superLongSpan bits.length) :
    superIsLong bits target superSlot = false := by
  unfold superIsLong
  have hspan := superSpan_le_length bits target hslot
  simp
  omega

/-- The "number of long supers" popcount is zero below the crossover. -/
theorem longFlagRank_zero_below_crossover
    (bits : List Bool) (target : Bool)
    (hsmall : bits.length <= superLongSpan bits.length) :
    forall m, m <= superSlotCount bits target ->
      RMQ.Succinct.rankPrefix true (longSuperFlagBits bits target) m = 0 := by
  intro m
  induction m with
  | zero => intro _; simp [RMQ.Succinct.rankPrefix]
  | succ m ih =>
      intro hm
      have hslot : m < superSlotCount bits target := by omega
      have hget := longSuperFlagBits_get? bits target hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true) (bits := longSuperFlagBits bits target)
          (n := m) hget
      have hfalse :=
        superIsLong_false_below_crossover bits target hslot hsmall
      rw [hrank, ih (by omega), hfalse]
      simp

/-- Hence the long-super relative table is EMPTY below the crossover. -/
theorem longSuperRelativeTable_empty_below_crossover
    (bits : List Bool) (target : Bool)
    (hsmall : bits.length <= superLongSpan bits.length) :
    (longSuperRelativeTable bits target).payload.length = 0 := by
  rw [longSuperRelativeTable_payload_length]
  rw [longFlagRank_zero_below_crossover bits target hsmall
    (superSlotCount bits target) (Nat.le_refl _)]
  simp

/-! ## Executed crossover table (bit length `n = 2 ^ k`) -/

#eval (List.range 20).map (fun k =>
  let n := 2 ^ k
  (k, n, superLongSpan n, decide (n <= superLongSpan n)))

#print axioms superSpan_le_length
#print axioms superIsLong_false_below_crossover
#print axioms longSuperRelativeTable_empty_below_crossover

end SdkG

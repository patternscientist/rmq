import RMQ.Core.WordRAM.Construction.Spec.Plan

/-!
# PRE-1 S5: reference facts for the access half

Machine-free specification layer (outside the builder firewall). The access
half reads the BP code only through the positions of its closes and the close
counts at word boundaries. `select_at_close` identifies the close at scan
position `p` as the occurrence numbered by the close count before `p`, so one
left-to-right scan fills `position shape.bpCode false k` for every `k`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.GenericSelect

/-- The close at scan position `p` is the occurrence counted before `p`. -/
theorem select_at_close (b : List Bool) {p : Nat} (hp : b[p]? = some false) :
    RMQ.Succinct.select false b (RMQ.Succinct.rankPrefix false b p) = some p := by
  have hsucc := rankPrefix_succ_eq_of_get? (target := false) hp
  simp only [if_true] at hsucc
  obtain ⟨q, hq⟩ := select_exists_of_lt_rankPrefix (target := false) (bits := b)
    (occurrence := RMQ.Succinct.rankPrefix false b p) (limit := p + 1) (by omega)
  have hrq := RMQ.Succinct.select_rankPrefix_eq hq
  have hrq1 := rankPrefix_succ_of_select hq
  have hqp : q = p := by
    by_cases hlt : q < p
    · have := RMQ.Succinct.rankPrefix_mono_limit false b (show q + 1 ≤ p by omega)
      omega
    · by_cases hgt : p < q
      · have := RMQ.Succinct.rankPrefix_mono_limit false b (show p + 1 ≤ q by omega)
        omega
      · omega
  rw [hqp] at hq
  exact hq

theorem position_at_close (b : List Bool) {p : Nat} (hp : b[p]? = some false) :
    position b false (RMQ.Succinct.rankPrefix false b p) = p :=
  position_eq_of_select b false (select_at_close b hp)

/-- One scan step of the close count. -/
theorem rankPrefix_false_succ (b : List Bool) {p : Nat} (hp : p < b.length) :
    RMQ.Succinct.rankPrefix false b (p + 1) =
      RMQ.Succinct.rankPrefix false b p + (if b[p] then 0 else 1) := by
  have hget : b[p]? = some b[p] := List.getElem?_eq_getElem hp
  rw [rankPrefix_succ_eq_of_get? (target := false) hget]
  cases b[p] <;> simp

/-- Over a BP code the close count is the size and the length is twice the size. -/
theorem bp_occurrenceCount (shape : CartesianShape) :
    occurrenceCount shape.bpCode false = shape.size :=
  SuccinctSpace.bpCode_rankFalse_full shape

theorem bp_rank_end (shape : CartesianShape) {q : Nat} (hq : shape.bpCode.length ≤ q) :
    RMQ.Succinct.rankPrefix false shape.bpCode q = shape.size := by
  rw [RMQ.Succinct.rankPrefix_eq_rankPrefix_length_of_length_le false _ hq]
  exact SuccinctSpace.bpCode_rankFalse_full shape

theorem bp_position_size (shape : CartesianShape) :
    position shape.bpCode false shape.size = shape.bpCode.length :=
  position_eq_length_of_count_le _ _ (Nat.le_of_eq (bp_occurrenceCount shape))

/-- Positions clamp at the occurrence count. -/
theorem position_min_size (shape : CartesianShape) (k : Nat) :
    position shape.bpCode false (min k shape.size) = position shape.bpCode false k := by
  by_cases hk : k ≤ shape.size
  · rw [Nat.min_eq_left hk]
  · rw [Nat.min_eq_right (by omega), bp_position_size,
      position_eq_length_of_count_le _ _ (by rw [bp_occurrenceCount]; omega)]

end RMQ.SuccinctFinal.PackedConstruction.Spec

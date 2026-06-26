import RMQ.Core.GenericSelect.SelectSource

/-!
# Generic select facts

Shape-free rank/select facts shared by the generic select construction.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

/-- Collect target-bit positions, continuing from an absolute base offset. -/
def allSelectPositionsFrom
    (target : Bool) : List Bool -> Nat -> List Nat
  | [], _base => []
  | bit :: rest, base =>
      let tail := allSelectPositionsFrom target rest (base + 1)
      if bit = target then base :: tail else tail

/-- Collect all absolute positions whose bit equals `target`. -/
def allSelectPositions (target : Bool) (bits : List Bool) : List Nat :=
  allSelectPositionsFrom target bits 0

theorem allSelectPositionsFrom_get?_eq_selectFrom
    (target : Bool) (bits : List Bool) (base occurrence : Nat) :
    (allSelectPositionsFrom target bits base)[occurrence]? =
      RMQ.Succinct.selectFrom target bits base occurrence := by
  induction bits generalizing base occurrence with
  | nil =>
      simp [allSelectPositionsFrom, RMQ.Succinct.selectFrom]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · cases occurrence with
        | zero =>
            simp [allSelectPositionsFrom, RMQ.Succinct.selectFrom, hbit]
        | succ occurrence =>
            simp [allSelectPositionsFrom, RMQ.Succinct.selectFrom, hbit,
              ih (base + 1) occurrence]
      · simp [allSelectPositionsFrom, RMQ.Succinct.selectFrom, hbit,
          ih (base + 1) occurrence]

theorem allSelectPositions_get?_eq_select
    (target : Bool) (bits : List Bool) (occurrence : Nat) :
    (allSelectPositions target bits)[occurrence]? =
      RMQ.Succinct.select target bits occurrence := by
  simp [allSelectPositions, RMQ.Succinct.select,
    allSelectPositionsFrom_get?_eq_selectFrom]

theorem allSelectPositionsFrom_length_eq_rankPrefix_length
    (target : Bool) (bits : List Bool) (base : Nat) :
    (allSelectPositionsFrom target bits base).length =
      RMQ.Succinct.rankPrefix target bits bits.length := by
  induction bits generalizing base with
  | nil =>
      simp [allSelectPositionsFrom, RMQ.Succinct.rankPrefix]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · simp [allSelectPositionsFrom, RMQ.Succinct.rankPrefix, hbit,
          ih (base + 1), Nat.add_comm]
      · simp [allSelectPositionsFrom, RMQ.Succinct.rankPrefix, hbit,
          ih (base + 1)]

theorem allSelectPositions_length_eq_rankPrefix_length
    (target : Bool) (bits : List Bool) :
    (allSelectPositions target bits).length =
      RMQ.Succinct.rankPrefix target bits bits.length := by
  simpa [allSelectPositions] using
    allSelectPositionsFrom_length_eq_rankPrefix_length target bits 0

/--
Rank at the end of a taken prefix agrees with rank in the original bitvector.

This version is convenient when a select proof first restricts the query to
`bits.take limit`: it avoids splitting on whether `limit` is past the payload
end at every use site.
-/
theorem rankPrefix_take_length_eq
    (target : Bool) (bits : List Bool) (limit : Nat) :
    RMQ.Succinct.rankPrefix target (bits.take limit)
        (bits.take limit).length =
      RMQ.Succinct.rankPrefix target bits limit := by
  by_cases hlimit : limit <= bits.length
  · have hlen : (bits.take limit).length = limit := by
      simp [List.length_take, Nat.min_eq_left hlimit]
    have hlimitTake : limit <= (bits.take limit).length := by
      rw [hlen]
      exact Nat.le_refl limit
    rw [hlen]
    exact RMQ.Succinct.rankPrefix_take_eq_of_le
      target bits hlimitTake
  · have hlen_le : bits.length <= limit := Nat.le_of_not_ge hlimit
    have htake : bits.take limit = bits := by
      exact List.take_of_length_le hlen_le
    rw [htake]
    exact
      (RMQ.Succinct.rankPrefix_eq_rankPrefix_length_of_length_le
        target bits hlen_le).symm

/-- A successful select contributes exactly one target bit at `pos + 1`. -/
theorem rankPrefix_succ_of_select
    {target : Bool} {bits : List Bool} {occurrence pos : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos) :
    RMQ.Succinct.rankPrefix target bits (pos + 1) = occurrence + 1 := by
  induction bits generalizing occurrence pos with
  | nil =>
      simp [RMQ.Succinct.select, RMQ.Succinct.selectFrom] at hselect
  | cons bit rest ih =>
      unfold RMQ.Succinct.select at hselect
      unfold RMQ.Succinct.selectFrom at hselect
      by_cases hbit : bit = target
      · rw [if_pos hbit] at hselect
        by_cases hocc : occurrence = 0
        · rw [if_pos hocc] at hselect
          injection hselect with hpos
          subst occurrence
          subst pos
          simp [RMQ.Succinct.rankPrefix, hbit]
        · rw [if_neg hocc] at hselect
          have hbase :=
            RMQ.Succinct.selectFrom_base_eq
              target rest 1 (occurrence - 1)
          rw [hbase] at hselect
          cases hsel :
              RMQ.Succinct.select target rest (occurrence - 1) with
          | none =>
              simp [hsel] at hselect
          | some inner =>
              simp [hsel] at hselect
              subst pos
              have hrec := ih hsel
              have hocc_pos : 0 < occurrence := Nat.pos_of_ne_zero hocc
              have hinnerSucc : 1 + inner = inner + 1 := by omega
              rw [hinnerSucc]
              simp [RMQ.Succinct.rankPrefix, hbit, hrec]
              omega
      · rw [if_neg hbit] at hselect
        have hbase := RMQ.Succinct.selectFrom_base_eq
          target rest 1 occurrence
        rw [hbase] at hselect
        cases hsel : RMQ.Succinct.select target rest occurrence with
        | none =>
            simp [hsel] at hselect
        | some inner =>
            simp [hsel] at hselect
            subst pos
            have hrec := ih hsel
            have hinnerSucc : 1 + inner = inner + 1 := by omega
            rw [hinnerSucc]
            simpa [RMQ.Succinct.rankPrefix, hbit] using hrec

/--
If a successful select answer lies before `limit`, then `limit` contains more
than `occurrence` target bits.
-/
theorem occurrence_lt_rankPrefix_of_select_lt
    {target : Bool} {bits : List Bool} {occurrence pos limit : Nat}
    (hselect : RMQ.Succinct.select target bits occurrence = some pos)
    (hpos : pos < limit) :
    occurrence < RMQ.Succinct.rankPrefix target bits limit := by
  have hsucc := rankPrefix_succ_of_select hselect
  have hmono :
      RMQ.Succinct.rankPrefix target bits (pos + 1) <=
        RMQ.Succinct.rankPrefix target bits limit :=
    RMQ.Succinct.rankPrefix_mono_limit
      target bits (Nat.succ_le_of_lt hpos)
  omega

theorem selectFrom_index_mono
    {target : Bool} {bits : List Bool} {base lo hi posLo posHi : Nat}
    (hle : lo <= hi)
    (hlo : RMQ.Succinct.selectFrom target bits base lo = some posLo)
    (hhi : RMQ.Succinct.selectFrom target bits base hi = some posHi) :
    posLo <= posHi := by
  induction bits generalizing base lo hi posLo posHi with
  | nil =>
      simp [RMQ.Succinct.selectFrom] at hlo
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · by_cases hlozero : lo = 0
        · subst lo
          simp [RMQ.Succinct.selectFrom, hbit] at hlo
          subst posLo
          exact (RMQ.Succinct.selectFrom_bounds hhi).left
        · have hhizero : hi ≠ 0 := by omega
          have htail : lo - 1 <= hi - 1 :=
            Nat.sub_le_sub_right hle 1
          have hloTail :
              RMQ.Succinct.selectFrom target rest (base + 1) (lo - 1) =
                some posLo := by
            simpa [RMQ.Succinct.selectFrom, hbit, hlozero] using hlo
          have hhiTail :
              RMQ.Succinct.selectFrom target rest (base + 1) (hi - 1) =
                some posHi := by
            simpa [RMQ.Succinct.selectFrom, hbit, hhizero] using hhi
          exact ih htail hloTail hhiTail
      · have hloTail :
            RMQ.Succinct.selectFrom target rest (base + 1) lo =
              some posLo := by
          simpa [RMQ.Succinct.selectFrom, hbit] using hlo
        have hhiTail :
            RMQ.Succinct.selectFrom target rest (base + 1) hi =
              some posHi := by
          simpa [RMQ.Succinct.selectFrom, hbit] using hhi
        exact ih hle hloTail hhiTail

theorem select_index_mono
    {target : Bool} {bits : List Bool} {lo hi posLo posHi : Nat}
    (hle : lo <= hi)
    (hlo : RMQ.Succinct.select target bits lo = some posLo)
    (hhi : RMQ.Succinct.select target bits hi = some posHi) :
    posLo <= posHi := by
  unfold RMQ.Succinct.select at *
  exact selectFrom_index_mono hle hlo hhi

theorem select_index_strict_mono
    {target : Bool} {bits : List Bool} {lo hi posLo posHi : Nat}
    (hlt : lo < hi)
    (hlo : RMQ.Succinct.select target bits lo = some posLo)
    (hhi : RMQ.Succinct.select target bits hi = some posHi) :
    posLo < posHi := by
  have hle : posLo <= posHi :=
    select_index_mono (Nat.le_of_lt hlt) hlo hhi
  have hne : posLo ≠ posHi := by
    intro heq
    have hloRank := rankPrefix_succ_of_select hlo
    have hhiRank := rankPrefix_succ_of_select hhi
    rw [<- heq] at hhiRank
    omega
  exact Nat.lt_of_le_of_ne hle hne

theorem rankPrefix_succ_eq_of_get?
    {target bit : Bool} {bits : List Bool} {n : Nat}
    (hget : bits[n]? = some bit) :
    RMQ.Succinct.rankPrefix target bits (n + 1) =
      RMQ.Succinct.rankPrefix target bits n +
        if bit = target then 1 else 0 := by
  induction bits generalizing n with
  | nil =>
      simp at hget
  | cons head tail ih =>
      cases n with
      | zero =>
          simp [RMQ.Succinct.rankPrefix] at hget ⊢
          subst bit
          omega
      | succ n =>
          simp at hget
          have htail := ih hget
          by_cases hhead : head = target
          · simp [RMQ.Succinct.rankPrefix, hhead, htail,
              Nat.add_comm, Nat.add_left_comm]
          · simp [RMQ.Succinct.rankPrefix, hhead, htail,
              Nat.add_comm]

theorem select_exists_of_lt_rankPrefix
    {target : Bool} {bits : List Bool} {occurrence limit : Nat}
    (hcount :
      occurrence < RMQ.Succinct.rankPrefix target bits limit) :
    exists pos, RMQ.Succinct.select target bits occurrence = some pos := by
  have hcountMin :
      occurrence <
        RMQ.Succinct.rankPrefix target bits
          (Nat.min limit bits.length) := by
    simpa [RMQ.Succinct.rankPrefix_min_length_eq] using hcount
  have htotal :
      occurrence <
        RMQ.Succinct.rankPrefix target bits bits.length := by
    exact Nat.lt_of_lt_of_le hcountMin
      (RMQ.Succinct.rankPrefix_mono_limit
        target bits (Nat.min_le_right limit bits.length))
  have hidx :
      occurrence < (allSelectPositions target bits).length := by
    simpa [allSelectPositions_length_eq_rankPrefix_length] using htotal
  refine ⟨(allSelectPositions target bits)[occurrence], ?_⟩
  have hget :
      (allSelectPositions target bits)[occurrence]? =
        some ((allSelectPositions target bits)[occurrence]) :=
    List.getElem?_eq_getElem hidx
  simpa [allSelectPositions_get?_eq_select] using hget

theorem select_none_of_rankPrefix_length_le
    {target : Bool} {bits : List Bool} {occurrence : Nat}
    (hcount :
      RMQ.Succinct.rankPrefix target bits bits.length <= occurrence) :
    RMQ.Succinct.select target bits occurrence = none := by
  have hget :
      (allSelectPositions target bits)[occurrence]? = none := by
    exact List.getElem?_eq_none (by
      simpa [allSelectPositions_length_eq_rankPrefix_length] using hcount)
  simpa [allSelectPositions_get?_eq_select] using hget

end RMQ.GenericSelect

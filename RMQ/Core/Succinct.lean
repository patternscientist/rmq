import RMQ.Core.Cost
import RMQ.Core.LowerBound
import RMQ.Core.PlusMinusOne
import RMQ.Core.RAM
import RMQ.Core.TableModel

/-!
# Succinct bit primitives

This module starts the bit-level layer needed for succinct RMQ/LCA upper
bounds.  It intentionally stays small: exact rank/select primitives over
`List Bool`, balanced-parentheses predicates, and the first bridge from
parenthesis bits to plus-minus-one depth traces.
-/

namespace RMQ

namespace Succinct

/-- Count occurrences of `target` in the first `limit` bits. -/
def rankPrefix (target : Bool) : List Bool -> Nat -> Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | bit :: rest, limit + 1 =>
      (if bit = target then 1 else 0) + rankPrefix target rest limit

theorem rankPrefix_zero (target : Bool) (bits : List Bool) :
    rankPrefix target bits 0 = 0 := by
  cases bits <;> rfl

theorem rankPrefix_nil (target : Bool) (limit : Nat) :
    rankPrefix target [] limit = 0 := by
  cases limit <;> rfl

theorem ram_boolRankPrefix_eq_rankPrefix
    (target : Bool) (bits : List Bool) (limit : Nat) :
    RAM.boolRankPrefix target bits limit = rankPrefix target bits limit := by
  induction bits generalizing limit with
  | nil =>
      cases limit <;> rfl
  | cons bit rest ih =>
      cases limit with
      | zero =>
          rfl
      | succ limit =>
          simp [RAM.boolRankPrefix, rankPrefix, ih]

theorem rankBoolWordPrefix_toCosted_run
    (target : Bool) (word : List Bool) (limit : Nat) :
    (RAM.rankBoolWordPrefix target word limit).toCosted.run =
      (rankPrefix target word limit, 1) := by
  rw [RAM.rankBoolWordPrefix_run, ram_boolRankPrefix_eq_rankPrefix]

theorem rankPrefix_le_limit
    (target : Bool) (bits : List Bool) (limit : Nat) :
    rankPrefix target bits limit <= limit := by
  induction bits generalizing limit with
  | nil =>
      rw [rankPrefix_nil]
      omega
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp [rankPrefix]
      | succ limit =>
          simp [rankPrefix]
          by_cases hbit : bit = target
          case pos =>
            simp [hbit]
            have hle := ih limit
            omega
          case neg =>
            simp [hbit]
            have hle := ih limit
            omega

theorem rankPrefix_le_length
    (target : Bool) (bits : List Bool) (limit : Nat) :
    rankPrefix target bits limit <= bits.length := by
  induction bits generalizing limit with
  | nil =>
      rw [rankPrefix_nil]
      omega
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp [rankPrefix]
      | succ limit =>
          simp [rankPrefix]
          by_cases hbit : bit = target
          case pos =>
            simp [hbit]
            have hle := ih limit
            omega
          case neg =>
            simp [hbit]
            have hle := ih limit
            omega

theorem rankPrefix_append_of_le
    (target : Bool) (xs ys : List Bool) {limit : Nat}
    (hlimit : limit <= xs.length) :
    rankPrefix target (xs ++ ys) limit = rankPrefix target xs limit := by
  induction xs generalizing limit with
  | nil =>
      have hzero : limit = 0 := by
        simp at hlimit
        omega
      subst limit
      simp [rankPrefix]
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp [rankPrefix]
      | succ limit =>
          have htail : limit <= rest.length := by
            simp at hlimit
            omega
          simp [rankPrefix, ih htail]

theorem rankPrefix_append_of_ge
    (target : Bool) (xs ys : List Bool) {limit : Nat}
    (hlimit : xs.length <= limit) :
    rankPrefix target (xs ++ ys) limit =
      rankPrefix target xs xs.length +
        rankPrefix target ys (limit - xs.length) := by
  induction xs generalizing limit with
  | nil =>
      simp [rankPrefix]
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp at hlimit
      | succ limit =>
          have htail : rest.length <= limit := by
            simp at hlimit
            omega
          have hsub : limit + 1 - (rest.length + 1) =
              limit - rest.length := by
            omega
          simp [rankPrefix, ih htail, hsub, Nat.add_assoc]

theorem rankPrefix_eq_rankPrefix_length_of_length_le
    (target : Bool) (bits : List Bool) {limit : Nat}
    (hlimit : bits.length <= limit) :
    rankPrefix target bits limit =
      rankPrefix target bits bits.length := by
  induction bits generalizing limit with
  | nil =>
      rw [rankPrefix_nil]
      rfl
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp at hlimit
      | succ limit =>
          have htail : rest.length <= limit := by
            simp at hlimit
            omega
          simp [rankPrefix, ih htail]

theorem rankPrefix_min_length_eq
    (target : Bool) (bits : List Bool) (limit : Nat) :
    rankPrefix target bits (Nat.min limit bits.length) =
      rankPrefix target bits limit := by
  by_cases hlimit : limit <= bits.length
  · simp [Nat.min_eq_left hlimit]
  · have hlen : bits.length <= limit := Nat.le_of_not_ge hlimit
    have hmin : Nat.min limit bits.length = bits.length :=
      Nat.min_eq_right hlen
    rw [hmin]
    exact (rankPrefix_eq_rankPrefix_length_of_length_le
      target bits hlen).symm

theorem rankPrefix_mono_limit
    (target : Bool) (bits : List Bool) {lo hi : Nat}
    (h : lo <= hi) :
    rankPrefix target bits lo <= rankPrefix target bits hi := by
  induction bits generalizing lo hi with
  | nil =>
      simp [rankPrefix_nil]
    | cons bit rest ih =>
      cases lo with
      | zero =>
          simp [rankPrefix]
      | succ lo =>
          cases hi with
          | zero =>
              omega
          | succ hi =>
              have htail : lo <= hi := by omega
              have hrec := ih htail
              by_cases hbit : bit = target
              · simp [rankPrefix, hbit]
                omega
              · simp [rankPrefix, hbit]
                exact hrec

theorem rankPrefix_take_eq_of_le
    (target : Bool) (bits : List Bool) {n limit : Nat}
    (hlimit : limit <= (bits.take n).length) :
    rankPrefix target (bits.take n) limit =
      rankPrefix target bits limit := by
  have h :=
    rankPrefix_append_of_le target (bits.take n) (bits.drop n)
      (limit := limit) hlimit
  have hbits : bits.take n ++ bits.drop n = bits :=
    List.take_append_drop n bits
  rw [hbits] at h
  exact h.symm

theorem rankPrefix_drop_eq_sub_of_le
    (target : Bool) (bits : List Bool) {start limit : Nat}
    (hstart : start <= limit) (hlimit : limit <= bits.length) :
    rankPrefix target (bits.drop start) (limit - start) =
      rankPrefix target bits limit - rankPrefix target bits start := by
  have hstartLen : start <= bits.length := Nat.le_trans hstart hlimit
  have htakeLen : (bits.take start).length = start := by
    simp [List.length_take, Nat.min_eq_left hstartLen]
  have htakeLimit : (bits.take start).length <= limit := by
    omega
  have hge :=
    rankPrefix_append_of_ge target (bits.take start) (bits.drop start)
      (limit := limit) htakeLimit
  have hbits : bits.take start ++ bits.drop start = bits :=
    List.take_append_drop start bits
  rw [hbits] at hge
  have hge' :
      rankPrefix target bits limit =
        rankPrefix target (bits.take start) start +
          rankPrefix target (bits.drop start) (limit - start) := by
    simpa [htakeLen] using hge
  have hstartEq :
      rankPrefix target bits start =
        rankPrefix target (bits.take start) start := by
    have hle : start <= (bits.take start).length := by omega
    have hprefix :=
      rankPrefix_append_of_le target (bits.take start) (bits.drop start)
        (limit := start) hle
    rw [hbits] at hprefix
    exact hprefix
  rw [hge', hstartEq]
  omega

/--
Find the zero-based index of the `occurrence`-th `target` bit, counting
occurrences from zero.
-/
def selectFrom (target : Bool) : List Bool -> Nat -> Nat -> Option Nat
  | [], _base, _occurrence => none
  | bit :: rest, base, occurrence =>
      if bit = target then
        if occurrence = 0 then
          some base
        else
          selectFrom target rest (base + 1) (occurrence - 1)
      else
        selectFrom target rest (base + 1) occurrence

/-- Select the zero-based `occurrence`-th `target` bit. -/
def select (target : Bool) (bits : List Bool) (occurrence : Nat) : Option Nat :=
  selectFrom target bits 0 occurrence

theorem ram_boolSelectFrom_eq_selectFrom
    (target : Bool) (bits : List Bool) (base occurrence : Nat) :
    RAM.boolSelectFrom target bits base occurrence =
      selectFrom target bits base occurrence := by
  induction bits generalizing base occurrence with
  | nil =>
      rfl
  | cons bit rest ih =>
      simp [RAM.boolSelectFrom, selectFrom]
      by_cases hbit : bit = target
      · simp [hbit]
        by_cases hocc : occurrence = 0
        · simp [hocc]
        · simp [hocc, ih]
      · simp [hbit, ih]

theorem ram_boolSelectInWord_eq_select
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    RAM.boolSelectInWord target word occurrence =
      select target word occurrence := by
  simp [RAM.boolSelectInWord, select, ram_boolSelectFrom_eq_selectFrom]

theorem selectBoolWord_toCosted_run
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    (RAM.selectBoolWord target word occurrence).toCosted.run =
      (select target word occurrence, 1) := by
  rw [RAM.selectBoolWord_run, ram_boolSelectInWord_eq_select]

theorem selectFrom_bounds
    {target : Bool} {bits : List Bool} {base occurrence idx : Nat}
    (hselect : selectFrom target bits base occurrence = some idx) :
    base <= idx /\ idx < base + bits.length := by
  induction bits generalizing base occurrence with
  | nil =>
      simp [selectFrom] at hselect
  | cons bit rest ih =>
      unfold selectFrom at hselect
      by_cases hbit : bit = target
      case pos =>
        rw [if_pos hbit] at hselect
        by_cases hocc : occurrence = 0
        case pos =>
          rw [if_pos hocc] at hselect
          injection hselect with hidx
          subst idx
          constructor <;> simp
        case neg =>
          rw [if_neg hocc] at hselect
          have hbounds := ih hselect
          cases hbounds with
          | intro hlo hhi =>
              constructor
              case left =>
                exact Nat.le_trans (Nat.le_succ base) hlo
              case right =>
                simp
                omega
      case neg =>
        rw [if_neg hbit] at hselect
        have hbounds := ih hselect
        cases hbounds with
        | intro hlo hhi =>
            constructor
            case left =>
              exact Nat.le_trans (Nat.le_succ base) hlo
            case right =>
              simp
              omega

theorem select_bounds
    {target : Bool} {bits : List Bool} {occurrence idx : Nat}
    (hselect : select target bits occurrence = some idx) :
    idx < bits.length := by
  unfold select at hselect
  have hbounds := selectFrom_bounds hselect
  omega

theorem selectFrom_none_of_length_le_occurrence
    (target : Bool) (bits : List Bool) (base occurrence : Nat)
    (h : bits.length <= occurrence) :
    selectFrom target bits base occurrence = none := by
  induction bits generalizing base occurrence with
  | nil =>
      simp [selectFrom]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · by_cases hocc : occurrence = 0
        · subst occurrence
          simp at h
        · have hrest : rest.length <= occurrence - 1 := by
            simp at h
            omega
          simp [selectFrom, hbit, hocc, ih (base + 1) (occurrence - 1)
            hrest]
      · have hrest : rest.length <= occurrence := by
          simp at h
          omega
        simp [selectFrom, hbit, ih (base + 1) occurrence hrest]

theorem select_none_of_length_le_occurrence
    {target : Bool} {bits : List Bool} {occurrence : Nat}
    (h : bits.length <= occurrence) :
    select target bits occurrence = none := by
  unfold select
  exact selectFrom_none_of_length_le_occurrence target bits 0 occurrence h

theorem select_min_length_eq
    (target : Bool) (bits : List Bool) (occurrence : Nat) :
    select target bits (Nat.min occurrence bits.length) =
      select target bits occurrence := by
  by_cases hocc : occurrence <= bits.length
  · simp [Nat.min_eq_left hocc]
  · have hlen : bits.length <= occurrence := by omega
    have hmin : Nat.min occurrence bits.length = bits.length := by
      exact Nat.min_eq_right hlen
    have hnoneMin :
        select target bits (Nat.min occurrence bits.length) = none := by
      rw [hmin]
      exact select_none_of_length_le_occurrence
        (target := target) (bits := bits) (occurrence := bits.length)
        (Nat.le_refl bits.length)
    have hnoneOccurrence :
        select target bits occurrence = none :=
      select_none_of_length_le_occurrence
        (target := target) (bits := bits) (occurrence := occurrence) hlen
    rw [hnoneMin, hnoneOccurrence]

theorem selectFrom_base_eq
    (target : Bool) (bits : List Bool) (base occurrence : Nat) :
    selectFrom target bits base occurrence =
      (select target bits occurrence).map (fun idx => base + idx) := by
  induction bits generalizing base occurrence with
  | nil =>
      simp [select, selectFrom]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · by_cases hocc : occurrence = 0
        · subst occurrence
          simp [select, selectFrom, hbit]
        · have hbase := ih (base + 1) (occurrence - 1)
          have hone := ih 1 (occurrence - 1)
          cases hsel : select target rest (occurrence - 1) with
          | none =>
              have hzero :
                  selectFrom target rest 0 (occurrence - 1) = none := by
                simpa [select] using hsel
              simp [select, selectFrom, hbit, hocc, hbase, hone, hzero]
          | some inner =>
              have hzero :
                  selectFrom target rest 0 (occurrence - 1) =
                    some inner := by
                simpa [select] using hsel
              simp [select, selectFrom, hbit, hocc, hbase, hone, hzero]
              omega
      · have hbase := ih (base + 1) occurrence
        have hone := ih 1 occurrence
        cases hsel : select target rest occurrence with
        | none =>
            have hzero :
                selectFrom target rest 0 occurrence = none := by
              simpa [select] using hsel
            simp [select, selectFrom, hbit, hbase, hone, hzero]
        | some inner =>
            have hzero :
                selectFrom target rest 0 occurrence = some inner := by
              simpa [select] using hsel
            simp [select, selectFrom, hbit, hbase, hone, hzero]
            omega

theorem selectFrom_of_select
    {target : Bool} {bits : List Bool} {occurrence idx base : Nat}
    (hselect : select target bits occurrence = some idx) :
    selectFrom target bits base occurrence = some (base + idx) := by
  rw [selectFrom_base_eq]
  simp [hselect]

theorem selectFrom_append_left_of_some
    {target : Bool} {xs ys : List Bool} {base occurrence idx : Nat}
    (hselect : selectFrom target xs base occurrence = some idx) :
    selectFrom target (xs ++ ys) base occurrence = some idx := by
  induction xs generalizing base occurrence idx with
  | nil =>
      simp [selectFrom] at hselect
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · by_cases hocc : occurrence = 0
        · simp [selectFrom, hbit, hocc] at hselect ⊢
          exact hselect
        · simp [selectFrom, hbit, hocc] at hselect ⊢
          exact ih hselect
      · simp [selectFrom, hbit] at hselect ⊢
        exact ih hselect

theorem select_append_left_of_some
    {target : Bool} {xs ys : List Bool} {occurrence idx : Nat}
    (hselect : select target xs occurrence = some idx) :
    select target (xs ++ ys) occurrence = some idx := by
  exact selectFrom_append_left_of_some hselect

theorem select_take_of_select_lt
    {target : Bool} {bits : List Bool} {occurrence idx n : Nat}
    (hselect : select target bits occurrence = some idx)
    (hidx : idx < n) :
    select target (bits.take n) occurrence = some idx := by
  induction bits generalizing occurrence idx n with
  | nil =>
      simp [select, selectFrom] at hselect
  | cons bit rest ih =>
      cases n with
      | zero =>
          omega
      | succ n =>
          unfold select at hselect ⊢
          unfold selectFrom at hselect
          by_cases hbit : bit = target
          · rw [if_pos hbit] at hselect
            by_cases hocc : occurrence = 0
            · rw [if_pos hocc] at hselect
              injection hselect with hidxEq
              subst idx
              subst occurrence
              simp [List.take, selectFrom, hbit]
            · rw [if_neg hocc] at hselect
              have hbase :=
                selectFrom_base_eq target rest 1 (occurrence - 1)
              rw [hbase] at hselect
              cases hrest : select target rest (occurrence - 1) with
              | none =>
                  simp [hrest] at hselect
              | some inner =>
                  simp [hrest] at hselect
                  subst idx
                  have hinner : inner < n := by omega
                  have htake :=
                    ih hrest hinner
                  have hfrom :=
                    selectFrom_of_select (base := 1) htake
                  simp [List.take, selectFrom, hbit, hocc]
                  exact hfrom
          · rw [if_neg hbit] at hselect
            have hbase := selectFrom_base_eq target rest 1 occurrence
            rw [hbase] at hselect
            cases hrest : select target rest occurrence with
            | none =>
                simp [hrest] at hselect
            | some inner =>
                simp [hrest] at hselect
                subst idx
                have hinner : inner < n := by omega
                have htake := ih hrest hinner
                have hfrom :=
                  selectFrom_of_select (base := 1) htake
                simp [List.take, selectFrom, hbit]
                exact hfrom

theorem select_rankPrefix_eq
    {target : Bool} {bits : List Bool} {occurrence idx : Nat}
    (hselect : select target bits occurrence = some idx) :
    rankPrefix target bits idx = occurrence := by
  induction bits generalizing occurrence idx with
  | nil =>
      simp [select, selectFrom] at hselect
  | cons bit rest ih =>
      unfold select at hselect
      unfold selectFrom at hselect
      by_cases hbit : bit = target
      · rw [if_pos hbit] at hselect
        by_cases hocc : occurrence = 0
        · rw [if_pos hocc] at hselect
          injection hselect with hidx
          subst occurrence
          subst idx
          simp [rankPrefix]
        · rw [if_neg hocc] at hselect
          have hbase :=
            selectFrom_base_eq target rest 1 (occurrence - 1)
          rw [hbase] at hselect
          cases hsel : select target rest (occurrence - 1) with
          | none =>
              simp [hsel] at hselect
          | some inner =>
              simp [hsel] at hselect
              subst idx
              have hrec := ih hsel
              have hocc_pos : 0 < occurrence := Nat.pos_of_ne_zero hocc
              have hsucc : 1 + inner = inner + 1 := by omega
              rw [hsucc]
              simp [rankPrefix, hbit, hrec]
              omega
      · rw [if_neg hbit] at hselect
        have hbase := selectFrom_base_eq target rest 1 occurrence
        rw [hbase] at hselect
        cases hsel : select target rest occurrence with
        | none =>
            simp [hsel] at hselect
        | some inner =>
            simp [hsel] at hselect
            subst idx
            have hrec := ih hsel
            have hsucc : 1 + inner = inner + 1 := by omega
            rw [hsucc]
            simp [rankPrefix, hbit, hrec]

theorem rankPrefix_le_occurrence_of_le_select
    {target : Bool} {bits : List Bool} {occurrence idx pos : Nat}
    (hselect : select target bits occurrence = some idx)
    (hpos : pos <= idx) :
    rankPrefix target bits pos <= occurrence := by
  have hmono := rankPrefix_mono_limit target bits hpos
  have hidx := select_rankPrefix_eq hselect
  omega

theorem selectFrom_append_right_after_count
    (target : Bool) (xs ys : List Bool) (base occurrence : Nat)
    (hcount : rankPrefix target xs xs.length <= occurrence) :
    selectFrom target (xs ++ ys) base occurrence =
      selectFrom target ys (base + xs.length)
        (occurrence - rankPrefix target xs xs.length) := by
  induction xs generalizing base occurrence with
  | nil =>
      simp [rankPrefix]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · have hocc : occurrence ≠ 0 := by
          intro hzero
          subst occurrence
          simp [rankPrefix, hbit] at hcount
        have htail :
            rankPrefix target rest rest.length <= occurrence - 1 := by
          simp [rankPrefix, hbit] at hcount
          omega
        have hsub :
            occurrence - 1 - rankPrefix target rest rest.length =
              occurrence - (1 + rankPrefix target rest rest.length) := by
          omega
        have hbase :
            base + 1 + rest.length = base + (rest.length + 1) := by
          omega
        simp [selectFrom, rankPrefix, hbit, hocc, ih (base + 1)
          (occurrence - 1) htail, hsub, hbase]
      · have htail :
            rankPrefix target rest rest.length <= occurrence := by
          simpa [rankPrefix, hbit] using hcount
        have hbase :
            base + 1 + rest.length = base + (rest.length + 1) := by
          omega
        simp [selectFrom, rankPrefix, hbit, ih (base + 1)
          occurrence htail, hbase]

theorem select_drop_eq_sub_of_select
    {target : Bool} {bits : List Bool}
    {occurrence idx start : Nat}
    (hselect : select target bits occurrence = some idx)
    (hstart : start <= idx)
    (hstartLen : start <= bits.length)
    (hrank : rankPrefix target bits start <= occurrence) :
    select target (bits.drop start)
        (occurrence - rankPrefix target bits start) =
      some (idx - start) := by
  let xs := bits.take start
  let ys := bits.drop start
  have hbits : xs ++ ys = bits := by
    simp [xs, ys, List.take_append_drop]
  have hxsLen : xs.length = start := by
    simp [xs, List.length_take, Nat.min_eq_left hstartLen]
  have hprefix :
      rankPrefix target xs xs.length =
        rankPrefix target bits start := by
    have hle : start <= xs.length := by omega
    have happ :=
      rankPrefix_append_of_le target xs ys (limit := start) hle
    rw [hbits] at happ
    rw [hxsLen]
    exact happ.symm
  have hcount :
      rankPrefix target xs xs.length <= occurrence := by
    rw [hprefix]
    exact hrank
  have happ :=
    selectFrom_append_right_after_count target xs ys 0 occurrence hcount
  have hselectFrom :
      selectFrom target ys start
          (occurrence - rankPrefix target bits start) =
        some idx := by
    have hsel := hselect
    unfold select at hsel
    rw [<- hbits] at hsel
    rw [happ] at hsel
    rw [hprefix] at hsel
    simpa [xs, ys, hxsLen] using hsel
  have hbase :=
    selectFrom_base_eq target ys start
      (occurrence - rankPrefix target bits start)
  rw [hbase] at hselectFrom
  have hlocalExists :
      exists inner,
        select target ys
            (occurrence - rankPrefix target bits start) = some inner /\
          start + inner = idx := by
    cases hlocal :
        select target ys
          (occurrence - rankPrefix target bits start) with
    | none =>
        simp [hlocal] at hselectFrom
    | some inner =>
        simp [hlocal] at hselectFrom
        exact ⟨inner, rfl, hselectFrom⟩
  rcases hlocalExists with ⟨inner, hlocal, hidx⟩
  have hlocalEq : inner = idx - start := by omega
  simpa [ys, hlocalEq] using hlocal

theorem select_drop_take_eq_sub_of_select
    {target : Bool} {bits : List Bool}
    {occurrence idx start width : Nat}
    (hselect : select target bits occurrence = some idx)
    (hstart : start <= idx)
    (hidxHi : idx < start + width)
    (hstartLen : start <= bits.length)
    (hrank : rankPrefix target bits start <= occurrence) :
    select target ((bits.drop start).take width)
        (occurrence - rankPrefix target bits start) =
      some (idx - start) := by
  have hdrop :=
    select_drop_eq_sub_of_select
      (target := target) (bits := bits)
      (occurrence := occurrence) (idx := idx) (start := start)
      hselect hstart hstartLen hrank
  have hlocalHi : idx - start < width := by omega
  exact select_take_of_select_lt hdrop hlocalHi

/-- `true` is an opening parenthesis in this bit-level model. -/
def isOpen (bit : Bool) : Prop :=
  bit = true

/-- `false` is a closing parenthesis in this bit-level model. -/
def isClose (bit : Bool) : Prop :=
  bit = false

/-- Prefix condition for balanced parentheses. -/
def BalancedPrefixes (bits : List Bool) : Prop :=
  forall pos,
    pos <= bits.length ->
      rankPrefix false bits pos <= rankPrefix true bits pos

/-- Balanced parentheses: every prefix is nonnegative and the final excess is zero. -/
def Balanced (bits : List Bool) : Prop :=
  BalancedPrefixes bits /\
    rankPrefix true bits bits.length =
      rankPrefix false bits bits.length

theorem balanced_nil : Balanced [] := by
  constructor
  · intro pos hpos
    have hzero : pos = 0 := by simp at hpos; omega
    subst pos
    simp [rankPrefix]
  · simp [rankPrefix]

theorem balanced_wrap_append
    {inside rest : List Bool}
    (hinside : Balanced inside) (hrest : Balanced rest) :
    Balanced (true :: inside ++ false :: rest) := by
  constructor
  · intro pos hpos
    cases pos with
    | zero =>
        simp [rankPrefix]
    | succ p =>
        have hpos' : p <= inside.length + (1 + rest.length) := by
          simp at hpos
          omega
        by_cases hp_inside : p <= inside.length
        · have hfalse :=
            rankPrefix_append_of_le false inside (false :: rest) hp_inside
          have htrue :=
            rankPrefix_append_of_le true inside (false :: rest) hp_inside
          have hprefix := hinside.1 p hp_inside
          simp [rankPrefix, hfalse, htrue]
          omega
        · have hp_ge : inside.length <= p := by omega
          have hfalse :=
            rankPrefix_append_of_ge false inside (false :: rest) hp_ge
          have htrue :=
            rankPrefix_append_of_ge true inside (false :: rest) hp_ge
          cases hk : p - inside.length with
          | zero =>
              have hp_le : p <= inside.length := by omega
              exact False.elim (hp_inside hp_le)
          | succ k =>
              have hk_rest : k <= rest.length := by
                omega
              have hrestPrefix := hrest.1 k hk_rest
              have hinsideFinal := hinside.2
              simp [rankPrefix, hfalse, htrue, hk]
              omega
  · have hinsideFinal := hinside.2
    have hrestFinal := hrest.2
    have hfalse :
        rankPrefix false (inside ++ false :: rest)
            (inside ++ false :: rest).length =
          rankPrefix false inside inside.length +
            rankPrefix false (false :: rest) (false :: rest).length := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rankPrefix_append_of_ge false inside (false :: rest)
          (limit := (inside ++ false :: rest).length) (by simp)
    have htrue :
        rankPrefix true (inside ++ false :: rest)
            (inside ++ false :: rest).length =
          rankPrefix true inside inside.length +
            rankPrefix true (false :: rest) (false :: rest).length := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        rankPrefix_append_of_ge true inside (false :: rest)
          (limit := (inside ++ false :: rest).length) (by simp)
    have htarget :
        1 + rankPrefix true (inside ++ false :: rest)
            (inside ++ false :: rest).length =
          rankPrefix false (inside ++ false :: rest)
            (inside ++ false :: rest).length := by
      rw [hfalse, htrue]
      simp [rankPrefix]
      omega
    simpa [rankPrefix] using htarget

structure BalancedParens where
  bits : List Bool
  balanced : Balanced bits

namespace BalancedParens

theorem close_rank_le_open_rank (parens : BalancedParens)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    rankPrefix false parens.bits pos <=
      rankPrefix true parens.bits pos := by
  exact parens.balanced.1 pos hpos

theorem final_rank_eq (parens : BalancedParens) :
    rankPrefix true parens.bits parens.bits.length =
      rankPrefix false parens.bits parens.bits.length := by
  exact parens.balanced.2

end BalancedParens

/--
Parenthesis bits also describe a plus-minus-one depth trace: open steps move
down one level and close steps move back up one level.
-/
def depthsFromParens (bits : List Bool) : List Int :=
  PlusMinusOne.traceFromSignature bits

theorem depthsFromParens_adjacent (bits : List Bool) :
    PlusMinusOne.IsDepthTrace (depthsFromParens bits) := by
  exact PlusMinusOne.traceFromSignature_adjacent bits

theorem depthsFromParens_length (bits : List Bool) :
    (depthsFromParens bits).length = bits.length + 1 := by
  simpa [depthsFromParens] using PlusMinusOne.traceFromSignature_length bits

/-- Package parenthesis bits as a normalized plus-minus-one RMQ input. -/
def plusMinusOneInputOfParens (bits : List Bool) : PlusMinusOne.Input where
  depths := depthsFromParens bits
  adjacent := depthsFromParens_adjacent bits

theorem plusMinusOneInputOfParens_depths (bits : List Bool) :
    (plusMinusOneInputOfParens bits).depths = depthsFromParens bits := by
  rfl

/-- Exact rank/select interface over a fixed bitvector. -/
structure RankSelectIndex (bits : List Bool) where
  rank : Bool -> Nat -> Nat
  rank_exact :
    forall target pos, rank target pos = rankPrefix target bits pos
  select : Bool -> Nat -> Option Nat
  select_exact :
    forall target occurrence,
      select target occurrence = Succinct.select target bits occurrence

namespace RankSelectIndex

/-- The canonical list-backed exact rank/select index. -/
def raw (bits : List Bool) : RankSelectIndex bits where
  rank target pos := rankPrefix target bits pos
  rank_exact := by
    intro target pos
    rfl
  select target occurrence := Succinct.select target bits occurrence
  select_exact := by
    intro target occurrence
    rfl

theorem rank_le_limit
    {bits : List Bool} (index : RankSelectIndex bits)
    (target : Bool) (pos : Nat) :
    index.rank target pos <= pos := by
  rw [index.rank_exact]
  exact rankPrefix_le_limit target bits pos

theorem select_bounds
    {bits : List Bool} (index : RankSelectIndex bits)
    {target : Bool} {occurrence idx : Nat}
    (hselect : index.select target occurrence = some idx) :
    idx < bits.length := by
  rw [index.select_exact] at hselect
  exact Succinct.select_bounds hselect

end RankSelectIndex

/--
Model-level packed bitvector with exact rank/select support.

The `payloadWords` field is a compact-storage accounting hook; the query-cost
theorems below use the same RAM/unit-cost indexed-access convention as the
other cost modules. The representation can therefore stand in for a future
word-packed bitvector without tying the proof layer to Lean's `List` runtime.
-/
structure PackedBitVector (bits : List Bool) where
  rankSelect : RankSelectIndex bits
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  payloadWords : Nat
  payloadWords_bound : payloadWords * wordSize <= bits.length + (wordSize - 1)

namespace PackedBitVector

/-- Canonical exact packed model. It uses one bit per word as a conservative baseline. -/
def raw (bits : List Bool) : PackedBitVector bits where
  rankSelect := RankSelectIndex.raw bits
  wordSize := 1
  wordSize_pos := by omega
  payloadWords := bits.length
  payloadWords_bound := by simp

/-- Number of payload bits occupied by the modeled packed words. -/
def payloadCapacityBits {bits : List Bool}
    (packed : PackedBitVector bits) : Nat :=
  packed.payloadWords * packed.wordSize

theorem payloadCapacityBits_le_length_plus_wordSlack
    {bits : List Bool} (packed : PackedBitVector bits) :
    packed.payloadCapacityBits <= bits.length + (packed.wordSize - 1) := by
  exact packed.payloadWords_bound

@[simp] theorem raw_payloadCapacityBits (bits : List Bool) :
    (raw bits).payloadCapacityBits = bits.length := by
  simp [payloadCapacityBits, raw]

/-- Semantic indexed bit view exposed by the packed model layer. -/
def bitAccess {bits : List Bool} (_packed : PackedBitVector bits) :
    TableModel.IndexedSeq Bool :=
  TableModel.IndexedSeq.ofList bits

@[simp] theorem bitAccess_length
    {bits : List Bool} (packed : PackedBitVector bits) :
    packed.bitAccess.length = bits.length := by
  rfl

@[simp] theorem bitAccess_get?
    {bits : List Bool} (packed : PackedBitVector bits) (i : Nat) :
    packed.bitAccess.get? i = bits[i]? := by
  rfl

theorem bitAccess_getCosted_run
    {bits : List Bool} (packed : PackedBitVector bits) (i : Nat) :
    (packed.bitAccess.getCosted i).run =
      (bits[i]?, TableModel.indexedReadCost) := by
  rfl

/-- Exact rank query through a packed bitvector. -/
def rank (packed : PackedBitVector bits) (target : Bool) (pos : Nat) : Nat :=
  packed.rankSelect.rank target pos

theorem rank_exact
    {bits : List Bool} (packed : PackedBitVector bits)
    (target : Bool) (pos : Nat) :
    packed.rank target pos = rankPrefix target bits pos := by
  exact packed.rankSelect.rank_exact target pos

/-- Exact select query through a packed bitvector. -/
def select
    (packed : PackedBitVector bits) (target : Bool) (occurrence : Nat) :
    Option Nat :=
  packed.rankSelect.select target occurrence

theorem select_exact
    {bits : List Bool} (packed : PackedBitVector bits)
    (target : Bool) (occurrence : Nat) :
    packed.select target occurrence =
      Succinct.select target bits occurrence := by
  exact packed.rankSelect.select_exact target occurrence

end PackedBitVector

/-- Packed balanced-parentheses bundle. -/
structure PackedBalancedParens where
  bits : List Bool
  balanced : Balanced bits
  packed : PackedBitVector bits

namespace PackedBalancedParens

/-- Canonical packed representation for an already-certified balanced bitstring. -/
def raw (parens : BalancedParens) : PackedBalancedParens where
  bits := parens.bits
  balanced := parens.balanced
  packed := PackedBitVector.raw parens.bits

end PackedBalancedParens

/--
Packed payload plus a fixed exact plus-minus-one RMQ table.

The `signature` is the counted bit payload.  The `packed` field supplies the
rank/select-facing packed view of that payload, while `table` is the universal
signature-table oracle used for the local RMQ answer.  This is intentionally a
model-level interface: it packages the standard succinct-RMQ split between
payload bits and a fixed decoder table without claiming that the raw Lean list
implementation of the table is itself constant time.
-/
structure PackedPlusMinusOneRMQ where
  signature : List Bool
  packed : PackedBitVector signature
  table : PlusMinusOne.SignatureTable

namespace PackedPlusMinusOneRMQ

/-- Canonical packed plus-minus-one RMQ model backed by the raw exact table. -/
def raw (signature : List Bool) : PackedPlusMinusOneRMQ where
  signature := signature
  packed := PackedBitVector.raw signature
  table := PlusMinusOne.SignatureTable.raw

/-- All delta signatures with a fixed number of bits. -/
def signatureUniverse (signatureLength : Nat) : List (List Bool) :=
  LowerBound.bitStrings signatureLength

theorem signatureUniverse_length (signatureLength : Nat) :
    (signatureUniverse signatureLength).length = 2 ^ signatureLength := by
  exact LowerBound.bitStrings_length signatureLength

theorem mem_signatureUniverse_of_length
    {signature : List Bool} {signatureLength : Nat}
    (hlen : signature.length = signatureLength) :
    List.Mem signature (signatureUniverse signatureLength) := by
  exact LowerBound.mem_bitStrings_of_length hlen

theorem signature_mem_own_universe (signature : List Bool) :
    List.Mem signature (signatureUniverse signature.length) := by
  exact mem_signatureUniverse_of_length rfl

/--
Number of local half-open query slots for a normalized trace represented by a
signature of length `signatureLength`.  The represented depth trace has
`signatureLength + 1` positions.
-/
def localQuerySlotBudget (signatureLength : Nat) : Nat :=
  (signatureLength + 1) * (signatureLength + 1)

/-- Row-major local query slot for a `(left,right)` pair. -/
def localQuerySlotIndex
    (signatureLength left right : Nat) : Nat :=
  left * (signatureLength + 1) + (right - 1)

theorem localQuerySlotIndex_lt
    {signatureLength left right : Nat}
    (hvalid : Cartesian.LocalValid (signatureLength + 1) left right) :
    localQuerySlotIndex signatureLength left right <
      localQuerySlotBudget signatureLength := by
  let width := signatureLength + 1
  have hright : right <= width := hvalid.2
  have hright_pos : 0 < right := by
    omega
  have hright_slot : right - 1 < width := by
    omega
  have hleft : left + 1 <= width := by
    have hlt : left < width := Nat.lt_of_lt_of_le hvalid.1 hright
    omega
  have hstep :
      left * width + (right - 1) < left * width + width := by
    exact Nat.add_lt_add_left hright_slot (left * width)
  have hrow :
      left * width + width = (left + 1) * width := by
    rw [Nat.succ_mul]
  have hbudget :
      (left + 1) * width <= width * width :=
    Nat.mul_le_mul_right width hleft
  have hlt : left * width + (right - 1) < width * width := by
    calc
      left * width + (right - 1) < left * width + width := hstep
      _ = (left + 1) * width := hrow
      _ <= width * width := hbudget
  simpa [localQuerySlotIndex, localQuerySlotBudget, width] using hlt

/-- Fixed universal-table slot budget for all signatures of this bit length. -/
def fixedTableSlotBudget (signatureLength : Nat) : Nat :=
  (signatureUniverse signatureLength).length *
    localQuerySlotBudget signatureLength

theorem fixedTableSlotBudget_eq
    (signatureLength : Nat) :
    fixedTableSlotBudget signatureLength =
      2 ^ signatureLength *
        ((signatureLength + 1) * (signatureLength + 1)) := by
  simp [fixedTableSlotBudget, signatureUniverse_length,
    localQuerySlotBudget]

/-- The counted payload view charges exactly the signature bits. -/
def payloadView : TableModel.PayloadView PackedPlusMinusOneRMQ where
  payloadBits state := state.signature
  payloadBitCount state := state.signature.length
  payload_length_le := by
    intro state
    exact Nat.le_refl _

@[simp] theorem payloadView_bits (state : PackedPlusMinusOneRMQ) :
    payloadView.payloadBits state = state.signature := by
  rfl

@[simp] theorem payloadView_count (state : PackedPlusMinusOneRMQ) :
    payloadView.payloadBitCount state = state.signature.length := by
  rfl

/-- Payload capacity induced by the packed-word accounting hook. -/
def payloadCapacityBits (state : PackedPlusMinusOneRMQ) : Nat :=
  state.packed.payloadCapacityBits

theorem payloadCapacityBits_le_signature_length_plus_wordSlack
    (state : PackedPlusMinusOneRMQ) :
    state.payloadCapacityBits <=
      state.signature.length + (state.packed.wordSize - 1) := by
  exact state.packed.payloadCapacityBits_le_length_plus_wordSlack

@[simp] theorem raw_payloadCapacityBits (signature : List Bool) :
    (raw signature).payloadCapacityBits = signature.length := by
  simp [payloadCapacityBits, raw]

/-- Forget the packed payload to the exact plus-minus-one backend contract. -/
def backend (state : PackedPlusMinusOneRMQ) :
    PlusMinusOne.Backend (plusMinusOneInputOfParens state.signature) where
  rmq := {
    State := Unit
    build := ()
    query := fun _ left right =>
      state.table.queryIndex? state.signature left right
    sound := by
      intro left right idx hquery
      have hsound :
          LeftmostArgMin (PlusMinusOne.traceFromSignature state.signature)
            left right idx :=
        PlusMinusOne.SignatureTable.queryIndex?_sound state.table hquery
      simpa [plusMinusOneInputOfParens_depths, depthsFromParens] using hsound
    complete := by
      intro left right idx harg
      have harg' :
          LeftmostArgMin (PlusMinusOne.traceFromSignature state.signature)
            left right idx := by
        simpa [plusMinusOneInputOfParens_depths, depthsFromParens] using harg
      exact
        PlusMinusOne.SignatureTable.queryIndex?_complete state.table harg'
    invalid_none := by
      intro left right hbad
      have hbadLocal :
          Not (Cartesian.LocalValid (state.signature.length + 1)
            left right) := by
        intro hvalid
        apply hbad
        constructor
        · exact hvalid.1
        · have hlen :
              (plusMinusOneInputOfParens state.signature).depths.length =
                state.signature.length + 1 := by
            simp [plusMinusOneInputOfParens_depths, depthsFromParens,
              PlusMinusOne.traceFromSignature_length]
          rw [hlen]
          exact hvalid.2
      exact PlusMinusOne.SignatureTable.queryIndex?_invalid
        state.table hbadLocal
  }

/-- Query the packed plus-minus-one RMQ model through its built backend. -/
def queryBuilt (state : PackedPlusMinusOneRMQ)
    (left right : Nat) : Option Nat :=
  PlusMinusOne.Backend.queryBuilt state.backend left right

theorem queryBuilt_eq_table
    (state : PackedPlusMinusOneRMQ) (left right : Nat) :
    state.queryBuilt left right =
      state.table.queryIndex? state.signature left right := by
  rfl

theorem queryBuilt_sound
    (state : PackedPlusMinusOneRMQ) {left right idx : Nat}
    (hquery : state.queryBuilt left right = some idx) :
    LeftmostArgMin (plusMinusOneInputOfParens state.signature).depths
      left right idx := by
  exact PlusMinusOne.Backend.queryBuilt_sound state.backend hquery

theorem queryBuilt_complete
    (state : PackedPlusMinusOneRMQ) {left right idx : Nat}
    (harg :
      LeftmostArgMin (plusMinusOneInputOfParens state.signature).depths
        left right idx) :
    state.queryBuilt left right = some idx := by
  exact PlusMinusOne.Backend.queryBuilt_complete state.backend harg

theorem queryBuilt_invalid_none
    (state : PackedPlusMinusOneRMQ) {left right : Nat}
    (hbad :
      Not (ValidRange (plusMinusOneInputOfParens state.signature).depths
        left right)) :
    state.queryBuilt left right = none := by
  exact PlusMinusOne.Backend.queryBuilt_invalid_none state.backend hbad

end PackedPlusMinusOneRMQ

/-- Encode an Euler depth move as a parenthesis bit. -/
def bitOfMove (move : Int) : Bool :=
  move = 1

theorem stepValue_bitOfMove
    {move : Int} (hmove : UnitDepthMove move) :
    PlusMinusOne.stepValue (bitOfMove move) = move := by
  rcases hmove with hmove | hmove
  · subst move
    simp [bitOfMove, PlusMinusOne.stepValue]
  · subst move
    simp [bitOfMove, PlusMinusOne.stepValue]

/-- Parenthesis bits obtained from Euler depth moves. -/
def bitsFromMoves (moves : List Int) : List Bool :=
  moves.map bitOfMove

theorem bitsFromMoves_length (moves : List Int) :
    (bitsFromMoves moves).length = moves.length := by
  simp [bitsFromMoves]

theorem traceFromSignatureAt_bitsFromMoves
    (start : Int) {moves : List Int}
    (hmoves : UnitDepthMoves moves) :
    PlusMinusOne.traceFromSignatureAt start (bitsFromMoves moves) =
      depthsFromMoves start moves := by
  induction moves generalizing start with
  | nil =>
      simp [bitsFromMoves, PlusMinusOne.traceFromSignatureAt, depthsFromMoves]
  | cons move rest ih =>
      rcases hmoves with ⟨hmove, hrest⟩
      have hstep := stepValue_bitOfMove hmove
      have htail := ih (start + move) hrest
      simp [bitsFromMoves, PlusMinusOne.traceFromSignatureAt, depthsFromMoves,
        hstep]
      simpa [bitsFromMoves] using htail

/-- Euler-tour parenthesis bits for a generated rose-tree Euler walk. -/
def eulerParens (tree : RoseTree) : List Bool :=
  bitsFromMoves tree.eulerMoves

theorem eulerParens_length (tree : RoseTree) :
    (eulerParens tree).length = tree.eulerMoves.length := by
  simp [eulerParens, bitsFromMoves_length]

theorem eulerParens_length_eq_eulerTrace_depths (tree : RoseTree) :
    (eulerParens tree).length + 1 = tree.eulerTrace.depths.length := by
  rw [eulerParens_length]
  simp [RoseTree.eulerTrace, RoseTree.eulerTraceAt, RoseTree.eulerDepthsAt,
    depthsFromMoves_length]

theorem eulerParens_length_eq_eulerTrace_nodes (tree : RoseTree) :
    (eulerParens tree).length + 1 = tree.eulerTrace.nodes.length := by
  rw [eulerParens_length]
  simpa [RoseTree.eulerTrace, RoseTree.eulerTraceAt] using
    (tree.eulerNodes_length_eq_moves).symm

mutual
  theorem eulerParens_balanced (tree : RoseTree) :
      Balanced (eulerParens tree) := by
    cases tree with
    | node _ children =>
        simpa [eulerParens, RoseTree.eulerMoves] using
          eulerParensForest_balanced children

  theorem eulerParensForest_balanced (forest : List RoseTree) :
      Balanced (bitsFromMoves (RoseTree.eulerMovesForest forest)) := by
    cases forest with
    | nil =>
        simpa [RoseTree.eulerMovesForest, bitsFromMoves] using balanced_nil
    | cons child rest =>
        have hchild : Balanced (eulerParens child) :=
          eulerParens_balanced child
        have hrest :
            Balanced (bitsFromMoves (RoseTree.eulerMovesForest rest)) :=
          eulerParensForest_balanced rest
        have hwrap :=
          balanced_wrap_append (inside := eulerParens child)
            (rest := bitsFromMoves (RoseTree.eulerMovesForest rest))
            hchild hrest
        simpa [eulerParens, bitsFromMoves, bitOfMove,
          RoseTree.eulerMovesForest] using hwrap
end

/-- Generated Euler-tour parentheses as a certified balanced bitstring. -/
def balancedEulerParens (tree : RoseTree) : BalancedParens where
  bits := eulerParens tree
  balanced := eulerParens_balanced tree

theorem depthsFromParens_eulerParens (tree : RoseTree) :
    depthsFromParens (eulerParens tree) = tree.eulerDepths := by
  unfold depthsFromParens eulerParens RoseTree.eulerDepths RoseTree.eulerDepthsAt
  exact traceFromSignatureAt_bitsFromMoves 0 (roseTree_eulerMoves_unit tree)

/-- Package Euler-tour parenthesis bits as a plus-minus-one RMQ input. -/
def plusMinusOneInputOfEulerParens (tree : RoseTree) : PlusMinusOne.Input :=
  plusMinusOneInputOfParens (eulerParens tree)

theorem plusMinusOneInputOfEulerParens_depths (tree : RoseTree) :
    (plusMinusOneInputOfEulerParens tree).depths = tree.eulerDepths := by
  simp [plusMinusOneInputOfEulerParens, plusMinusOneInputOfParens_depths,
    depthsFromParens_eulerParens]

theorem plusMinusOneInputOfEulerParens_depths_eq_trace (tree : RoseTree) :
    (plusMinusOneInputOfEulerParens tree).depths =
      tree.eulerTrace.depths := by
  simp [plusMinusOneInputOfEulerParens_depths, RoseTree.eulerTrace,
    RoseTree.eulerTraceAt, RoseTree.eulerDepths]

theorem plusMinusOneInputOfEulerParens_adjacent (tree : RoseTree) :
    PlusMinusOne.IsDepthTrace
      (plusMinusOneInputOfEulerParens tree).depths := by
  exact (plusMinusOneInputOfEulerParens tree).adjacent

/-- Packed exact rank/select index over the generated Euler-tour parentheses. -/
def packedEulerParens (tree : RoseTree) :
    PackedBitVector (eulerParens tree) :=
  PackedBitVector.raw (eulerParens tree)

/-- Packed certified balanced parentheses for the generated Euler tour. -/
def packedBalancedEulerParens (tree : RoseTree) : PackedBalancedParens :=
  PackedBalancedParens.raw (balancedEulerParens tree)

theorem packedBalancedEulerParens_bits (tree : RoseTree) :
    (packedBalancedEulerParens tree).bits = eulerParens tree := by
  rfl

/-- Packed plus-minus-one RMQ model over generated Euler-tour parentheses. -/
def packedEulerParensRMQ (tree : RoseTree) : PackedPlusMinusOneRMQ :=
  PackedPlusMinusOneRMQ.raw (eulerParens tree)

/-- Exact plus-minus-one backend supplied by the packed Euler-parentheses RMQ model. -/
def packedEulerParensBackend (tree : RoseTree) :
    PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree) :=
  (packedEulerParensRMQ tree).backend

theorem packedEulerParensBackend_queryBuilt_eq_table
    (tree : RoseTree) (left right : Nat) :
    PlusMinusOne.Backend.queryBuilt (packedEulerParensBackend tree)
        left right =
      PlusMinusOne.SignatureTable.raw.queryIndex?
        (eulerParens tree) left right := by
  rfl

theorem packedEulerParensRMQ_payloadBitCount_eq
    (tree : RoseTree) :
    PackedPlusMinusOneRMQ.payloadView.payloadBitCount
        (packedEulerParensRMQ tree) =
      (eulerParens tree).length := by
  rfl

theorem packedEulerParensRMQ_payloadBitCount_add_one_eq_trace_nodes
    (tree : RoseTree) :
    PackedPlusMinusOneRMQ.payloadView.payloadBitCount
        (packedEulerParensRMQ tree) + 1 =
      tree.eulerTrace.nodes.length := by
  simpa [packedEulerParensRMQ_payloadBitCount_eq] using
    eulerParens_length_eq_eulerTrace_nodes tree

theorem packedEulerParensRMQ_payloadCapacityBits_eq
    (tree : RoseTree) :
    (packedEulerParensRMQ tree).payloadCapacityBits =
      (eulerParens tree).length := by
  change (PackedBitVector.raw (eulerParens tree)).payloadCapacityBits =
    (eulerParens tree).length
  exact PackedBitVector.raw_payloadCapacityBits (eulerParens tree)

theorem packedEulerParensRMQ_payloadCapacityBits_add_one_eq_trace_nodes
    (tree : RoseTree) :
    (packedEulerParensRMQ tree).payloadCapacityBits + 1 =
      tree.eulerTrace.nodes.length := by
  simpa [packedEulerParensRMQ_payloadCapacityBits_eq] using
    eulerParens_length_eq_eulerTrace_nodes tree

/-- Packed Euler-parentheses PM1 payload profile. -/
theorem packedEulerParensRMQ_space_profile
    (tree : RoseTree) :
    PackedPlusMinusOneRMQ.payloadView.payloadBitCount
        (packedEulerParensRMQ tree) + 1 =
      tree.eulerTrace.nodes.length /\
      (packedEulerParensRMQ tree).payloadCapacityBits + 1 =
        tree.eulerTrace.nodes.length := by
  exact ⟨
    packedEulerParensRMQ_payloadBitCount_add_one_eq_trace_nodes tree,
    packedEulerParensRMQ_payloadCapacityBits_add_one_eq_trace_nodes tree⟩

end Succinct

end RMQ

import RMQ.Core.PlusMinusOne

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

end Succinct

end RMQ

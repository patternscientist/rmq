import RMQ.Core.SuccinctClose.RangeSummary

/-!
# PRE-1 S1: the Dyck prefix law of the BP code

Machine-free specification layer (outside the builder firewall).
`SuccinctClose.bpExcessAt` is a truncated `Nat` subtraction of close rank from
open rank. A charged machine that keeps a running excess counter must never
subtract below zero, so the stage proofs need the prefix law at every position,
not only inside the code: `bpCode_closes_le_opens` holds for all `p`, including
positions past the end, where both ranks saturate.

The running-excess step laws say that one scan position changes the excess by
exactly `+1` at an opening bit and `-1` at a closing bit, and that the counter is
at least one before every closing bit, so the machine's `sub` never underflows.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.Succinct

/-- One-position rank step over an arbitrary bit list, total in `p`. -/
theorem rankPrefix_succ_getElem? (target : Bool) :
    ∀ (bits : List Bool) (p : Nat),
      rankPrefix target bits (p + 1) =
        rankPrefix target bits p +
          (match bits[p]? with
           | some bit => if bit = target then 1 else 0
           | none => 0)
  | [], p => by simp [rankPrefix_nil]
  | bit :: rest, 0 => by simp [rankPrefix, rankPrefix_zero]
  | bit :: rest, p + 1 => by
      have ih := rankPrefix_succ_getElem? target rest p
      simp only [rankPrefix, List.getElem?_cons_succ] at ih ⊢
      rw [ih, Nat.add_assoc]

/-- Both ranks over the whole BP code equal the number of nodes. -/
theorem bpCode_rank_full (b : Bool) (T : CartesianShape) :
    rankPrefix b T.bpCode T.bpCode.length = T.size := by
  induction T with
  | empty => simp [CartesianShape.bpCode, CartesianShape.size, rankPrefix_nil]
  | node left right ihl ihr =>
      show rankPrefix b (true :: (left.bpCode ++ false :: right.bpCode))
          ((left.bpCode ++ false :: right.bpCode).length + 1) = _
      rw [rankPrefix, rankPrefix_append_of_ge b _ _ (by simp), ihl,
        show (left.bpCode ++ false :: right.bpCode).length - left.bpCode.length =
          right.bpCode.length + 1 by simp, rankPrefix, ihr]
      cases b <;> simp [CartesianShape.size] <;> omega

/-- **Dyck prefix law.** At every prefix length, closes never exceed opens. -/
theorem bpCode_closes_le_opens (T : CartesianShape) (p : Nat) :
    rankPrefix false T.bpCode p ≤ rankPrefix true T.bpCode p := by
  induction T generalizing p with
  | empty => simp [CartesianShape.bpCode, rankPrefix_nil]
  | node left right ihl ihr =>
      cases p with
      | zero => simp [rankPrefix_zero]
      | succ p =>
          have e1 : rankPrefix false (CartesianShape.node left right).bpCode (p + 1) =
              rankPrefix false (left.bpCode ++ false :: right.bpCode) p := by
            show (if true = false then 1 else 0) + _ = _
            exact Nat.zero_add _
          have e2 : rankPrefix true (CartesianShape.node left right).bpCode (p + 1) =
              rankPrefix true (left.bpCode ++ false :: right.bpCode) p + 1 := by
            show (if true = true then 1 else 0) + _ = _
            exact Nat.add_comm _ _
          rw [e1, e2]
          by_cases hp : p ≤ left.bpCode.length
          · rw [rankPrefix_append_of_le _ _ _ hp, rankPrefix_append_of_le _ _ _ hp]
            have := ihl p
            omega
          · have hge : left.bpCode.length ≤ p := by omega
            rw [rankPrefix_append_of_ge _ _ _ hge, rankPrefix_append_of_ge _ _ _ hge,
              bpCode_rank_full, bpCode_rank_full]
            obtain ⟨q, hq⟩ : ∃ q, p - left.bpCode.length = q + 1 :=
              ⟨p - left.bpCode.length - 1, by omega⟩
            rw [hq]
            have e3 : rankPrefix false (false :: right.bpCode) (q + 1) =
                1 + rankPrefix false right.bpCode q := rfl
            have e4 : rankPrefix true (false :: right.bpCode) (q + 1) =
                rankPrefix true right.bpCode q := by
              show (if false = true then 1 else 0) + _ = _
              exact Nat.zero_add _
            rw [e3, e4]
            have := ihr q
            omega

/-- Truncation never fires: excess plus close rank is the open rank. -/
theorem bpExcessAt_add_closes (T : CartesianShape) (p : Nat) :
    SuccinctClose.bpExcessAt T p + rankPrefix false T.bpCode p =
      rankPrefix true T.bpCode p := by
  unfold SuccinctClose.bpExcessAt
  have := bpCode_closes_le_opens T p
  omega

/-- Running excess, opening bit: the counter increments. -/
theorem bpExcessAt_succ_of_open (T : CartesianShape) {p : Nat}
    (h : T.bpCode[p]? = some true) :
    SuccinctClose.bpExcessAt T (p + 1) = SuccinctClose.bpExcessAt T p + 1 := by
  have ht := rankPrefix_succ_getElem? true T.bpCode p
  have hf := rankPrefix_succ_getElem? false T.bpCode p
  rw [h] at ht hf
  have ht' : rankPrefix true T.bpCode (p + 1) = rankPrefix true T.bpCode p + 1 := ht
  have hf' : rankPrefix false T.bpCode (p + 1) = rankPrefix false T.bpCode p + 0 := hf
  have h0 := bpCode_closes_le_opens T p
  unfold SuccinctClose.bpExcessAt
  omega

/-- Running excess, closing bit: the counter is positive before the bit and
decrements, so a machine `sub` by one never underflows. -/
theorem bpExcessAt_succ_of_close (T : CartesianShape) {p : Nat}
    (h : T.bpCode[p]? = some false) :
    1 ≤ SuccinctClose.bpExcessAt T p ∧
      SuccinctClose.bpExcessAt T (p + 1) = SuccinctClose.bpExcessAt T p - 1 := by
  have ht := rankPrefix_succ_getElem? true T.bpCode p
  have hf := rankPrefix_succ_getElem? false T.bpCode p
  rw [h] at ht hf
  have ht' : rankPrefix true T.bpCode (p + 1) = rankPrefix true T.bpCode p + 0 := ht
  have hf' : rankPrefix false T.bpCode (p + 1) = rankPrefix false T.bpCode p + 1 := hf
  have h1 := bpCode_closes_le_opens T (p + 1)
  unfold SuccinctClose.bpExcessAt
  omega

/-- Past the end the excess stays at its final value zero. -/
theorem bpExcessAt_of_length_le (T : CartesianShape) {p : Nat}
    (h : T.bpCode.length ≤ p) : SuccinctClose.bpExcessAt T p = 0 := by
  unfold SuccinctClose.bpExcessAt
  rw [rankPrefix_eq_rankPrefix_length_of_length_le _ _ h,
    rankPrefix_eq_rankPrefix_length_of_length_le _ _ h, bpCode_rank_full, bpCode_rank_full]
  simp

end RMQ.SuccinctFinal.PackedConstruction.Spec
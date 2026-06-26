import RMQ.Core.EncodingLowerBound
import RMQ.Core.Succinct

/-!
# Cartesian-shape balanced-parentheses bridges

Balanced-parentheses codes for Cartesian shapes, close-position lookup by
inorder index, and the bridge between false-select over the BP code and that
close lookup.
-/

namespace RMQ

namespace SuccinctSpace

/-- Cartesian-shape balanced-parentheses codes are genuinely balanced. -/
theorem bpCode_balanced (shape : Cartesian.CartesianShape) :
    Succinct.Balanced shape.bpCode := by
  induction shape with
  | empty =>
      simpa [Cartesian.CartesianShape.bpCode] using Succinct.balanced_nil
  | node left right ihleft ihright =>
      simpa [Cartesian.CartesianShape.bpCode] using
        Succinct.balanced_wrap_append
          (inside := left.bpCode) (rest := right.bpCode)
          ihleft ihright

/-- Package a Cartesian shape's BP code as a balanced-parentheses bitvector. -/
def bpParensOfShape (shape : Cartesian.CartesianShape) :
    Succinct.BalancedParens where
  bits := shape.bpCode
  balanced := bpCode_balanced shape

theorem bpParensOfShape_bits (shape : Cartesian.CartesianShape) :
    (bpParensOfShape shape).bits = shape.bpCode := by
  rfl

theorem bpParensOfShape_bits_length_of_shapeOfSize
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : Cartesian.ShapeOfSize n shape) :
    (bpParensOfShape shape).bits.length = 2 * n := by
  exact Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshape

/-- Close-parenthesis position for the node with the given inorder index. -/
def bpCloseOfInorder? :
    Cartesian.CartesianShape -> Nat -> Option Nat
  | Cartesian.CartesianShape.empty, _ => none
  | Cartesian.CartesianShape.node left right, idx =>
      if idx < left.size then
        (bpCloseOfInorder? left idx).map (fun pos => pos + 1)
      else if idx = left.size then
        some (left.bpCode.length + 1)
      else
        (bpCloseOfInorder? right (idx - left.size - 1)).map
          (fun pos => left.bpCode.length + 2 + pos)

theorem bpCloseOfInorder?_some_of_lt
    (shape : Cartesian.CartesianShape) {idx : Nat}
    (hidx : idx < shape.size) :
    exists pos, bpCloseOfInorder? shape idx = some pos := by
  induction shape generalizing idx with
  | empty =>
      simp [Cartesian.CartesianShape.size] at hidx
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · rcases ihleft hleft with ⟨pos, hpos⟩
        exact ⟨pos + 1, by
          simp [bpCloseOfInorder?, hleft, hpos]⟩
      · by_cases hroot : idx = left.size
        · exact ⟨left.bpCode.length + 1, by
            simp [bpCloseOfInorder?, hroot]⟩
        · have hright : idx - left.size - 1 < right.size := by
            simp [Cartesian.CartesianShape.size] at hidx
            omega
          rcases ihright hright with ⟨pos, hpos⟩
          exact ⟨left.bpCode.length + 2 + pos, by
            simp [bpCloseOfInorder?, hleft, hroot, hpos]⟩

theorem bpCloseOfInorder?_bounds
    (shape : Cartesian.CartesianShape) {idx pos : Nat}
    (hpos : bpCloseOfInorder? shape idx = some pos) :
    pos < shape.bpCode.length := by
  induction shape generalizing idx pos with
  | empty =>
      simp [bpCloseOfInorder?] at hpos
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · cases hrec : bpCloseOfInorder? left idx with
        | none =>
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
        | some inner =>
            have hinner := ihleft hrec
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
            subst pos
            simp [Cartesian.CartesianShape.bpCode]
            omega
      · by_cases hroot : idx = left.size
        · simp [bpCloseOfInorder?, hroot] at hpos
          subst pos
          simp [Cartesian.CartesianShape.bpCode]
        · cases hrec :
            bpCloseOfInorder? right (idx - left.size - 1) with
          | none =>
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
          | some inner =>
              have hinner := ihright hrec
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
              subst pos
              simp [Cartesian.CartesianShape.bpCode]
              omega

theorem bpCode_rankFalse_full (shape : Cartesian.CartesianShape) :
    Succinct.rankPrefix false shape.bpCode shape.bpCode.length =
      shape.size := by
  induction shape with
  | empty =>
      simp [Cartesian.CartesianShape.bpCode,
        Cartesian.CartesianShape.size, Succinct.rankPrefix]
  | node left right ihleft ihright =>
      have htail :
          Succinct.rankPrefix false
              (left.bpCode ++ false :: right.bpCode)
              (left.bpCode ++ false :: right.bpCode).length =
            left.size + (1 + right.size) := by
        have happend :=
          Succinct.rankPrefix_append_of_ge false left.bpCode
            (false :: right.bpCode)
            (limit := (left.bpCode ++ false :: right.bpCode).length)
            (by simp)
        have hright :
            Succinct.rankPrefix false (false :: right.bpCode)
                (false :: right.bpCode).length =
              1 + right.size := by
          simp [Succinct.rankPrefix, ihright]
        have hright' :
            Succinct.rankPrefix false (false :: right.bpCode)
                ((left.bpCode ++ false :: right.bpCode).length -
                  left.bpCode.length) =
              1 + right.size := by
          simpa using hright
        rw [happend]
        rw [ihleft, hright']
      calc
        Succinct.rankPrefix false
            (Cartesian.CartesianShape.node left right).bpCode
            (Cartesian.CartesianShape.node left right).bpCode.length =
          Succinct.rankPrefix false
            (left.bpCode ++ false :: right.bpCode)
            (left.bpCode ++ false :: right.bpCode).length := by
            simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix]
        _ = left.size + (1 + right.size) := htail
        _ = (Cartesian.CartesianShape.node left right).size := by
            simp [Cartesian.CartesianShape.size]
            omega

theorem bpCloseOfInorder?_rankFalse_succ
    (shape : Cartesian.CartesianShape) {idx pos : Nat}
    (hpos : bpCloseOfInorder? shape idx = some pos) :
    Succinct.rankPrefix false shape.bpCode (pos + 1) = idx + 1 := by
  induction shape generalizing idx pos with
  | empty =>
      simp [bpCloseOfInorder?] at hpos
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · cases hrec : bpCloseOfInorder? left idx with
        | none =>
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
        | some inner =>
            have hinnerBound :
                inner < left.bpCode.length :=
              bpCloseOfInorder?_bounds left hrec
            have hrank := ihleft hrec
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
            subst pos
            have happend :
                Succinct.rankPrefix false
                    (left.bpCode ++ false :: right.bpCode)
                    (inner + 1) =
                  Succinct.rankPrefix false left.bpCode (inner + 1) :=
              Succinct.rankPrefix_append_of_le false left.bpCode
                (false :: right.bpCode) (limit := inner + 1) (by omega)
            calc
              Succinct.rankPrefix false
                  (Cartesian.CartesianShape.node left right).bpCode
                  (inner + 1 + 1) =
                Succinct.rankPrefix false
                    (left.bpCode ++ false :: right.bpCode)
                    (inner + 1) := by
                  simp [Cartesian.CartesianShape.bpCode,
                    Succinct.rankPrefix, Nat.add_assoc]
              _ = Succinct.rankPrefix false left.bpCode (inner + 1) := happend
              _ = idx + 1 := hrank
      · by_cases hroot : idx = left.size
        · simp [bpCloseOfInorder?, hroot] at hpos
          subst pos
          have happend :
              Succinct.rankPrefix false
                  (left.bpCode ++ false :: right.bpCode)
                  (left.bpCode.length + 1) =
                Succinct.rankPrefix false left.bpCode left.bpCode.length +
                  Succinct.rankPrefix false (false :: right.bpCode) 1 := by
            have hge :
                left.bpCode.length <= left.bpCode.length + 1 := by omega
            have happ :=
              Succinct.rankPrefix_append_of_ge false left.bpCode
                (false :: right.bpCode)
                (limit := left.bpCode.length + 1) hge
            simpa using happ
          calc
            Succinct.rankPrefix false
                (Cartesian.CartesianShape.node left right).bpCode
                (left.bpCode.length + 1 + 1) =
              Succinct.rankPrefix false
                  (left.bpCode ++ false :: right.bpCode)
                  (left.bpCode.length + 1) := by
                simp [Cartesian.CartesianShape.bpCode,
                  Succinct.rankPrefix, Nat.add_assoc]
            _ = left.size + 1 := by
                rw [happend, bpCode_rankFalse_full left]
                simp [Succinct.rankPrefix]
            _ = idx + 1 := by
                omega
        · cases hrec :
            bpCloseOfInorder? right (idx - left.size - 1) with
          | none =>
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
          | some inner =>
              have hrank := ihright hrec
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
              subst pos
              have happend :
                  Succinct.rankPrefix false
                      (left.bpCode ++ false :: right.bpCode)
                      (left.bpCode.length + 2 + inner) =
                    Succinct.rankPrefix false left.bpCode
                        left.bpCode.length +
                      Succinct.rankPrefix false (false :: right.bpCode)
                        (2 + inner) := by
                have hge :
                    left.bpCode.length <=
                      left.bpCode.length + 2 + inner := by omega
                have happ :=
                  Succinct.rankPrefix_append_of_ge false left.bpCode
                    (false :: right.bpCode)
                    (limit := left.bpCode.length + 2 + inner) hge
                have hsub :
                    left.bpCode.length + 2 + inner -
                        left.bpCode.length =
                      2 + inner := by
                  omega
                simpa [hsub] using happ
              have htail :
                  Succinct.rankPrefix false (false :: right.bpCode)
                      (2 + inner) =
                    1 +
                      Succinct.rankPrefix false right.bpCode
                        (inner + 1) := by
                have htailRaw :
                    Succinct.rankPrefix false (false :: right.bpCode)
                        ((inner + 1) + 1) =
                      1 +
                        Succinct.rankPrefix false right.bpCode
                          (inner + 1) := by
                  simp [Succinct.rankPrefix]
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using htailRaw
              have hlead :
                  Succinct.rankPrefix false
                      (true :: (left.bpCode ++ false :: right.bpCode))
                      (left.bpCode.length + 2 + inner + 1) =
                    Succinct.rankPrefix false
                      (left.bpCode ++ false :: right.bpCode)
                      (left.bpCode.length + 2 + inner) := by
                simp [Succinct.rankPrefix]
              calc
                Succinct.rankPrefix false
                    (Cartesian.CartesianShape.node left right).bpCode
                    (left.bpCode.length + 2 + inner + 1) =
                  Succinct.rankPrefix false
                      (left.bpCode ++ false :: right.bpCode)
                      (left.bpCode.length + 2 + inner) := by
                    simpa [Cartesian.CartesianShape.bpCode,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using hlead
                _ = left.size + (1 +
                    Succinct.rankPrefix false right.bpCode (inner + 1)) := by
                    rw [happend, bpCode_rankFalse_full left, htail]
                _ = idx + 1 := by
                    rw [hrank]
                    omega

theorem select_false_bpCode_eq_bpCloseOfInorder?
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    Succinct.select false shape.bpCode idx =
      bpCloseOfInorder? shape idx := by
  induction shape generalizing idx with
  | empty =>
      simp [Cartesian.CartesianShape.bpCode, bpCloseOfInorder?,
        Succinct.select, Succinct.selectFrom]
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · rcases bpCloseOfInorder?_some_of_lt left hleft with
          ⟨leftClose, hleftClose⟩
        have hleftSelect :
            Succinct.select false left.bpCode idx = some leftClose := by
          simpa [hleftClose] using ihleft idx
        have hshift :
            Succinct.selectFrom false left.bpCode 1 idx =
              some (1 + leftClose) :=
          Succinct.selectFrom_of_select hleftSelect
        have happend :
            Succinct.selectFrom false
                (left.bpCode ++ false :: right.bpCode) 1 idx =
              some (1 + leftClose) :=
          Succinct.selectFrom_append_left_of_some
            (ys := false :: right.bpCode) hshift
        simp [Cartesian.CartesianShape.bpCode, bpCloseOfInorder?,
          Succinct.select, Succinct.selectFrom, hleft, hleftClose, happend]
        omega
      · by_cases hroot : idx = left.size
        · have hcount :
              Succinct.rankPrefix false left.bpCode left.bpCode.length <=
                idx := by
            rw [bpCode_rankFalse_full left]
            omega
          have hdrop :=
            Succinct.selectFrom_append_right_after_count false
              left.bpCode (false :: right.bpCode) 1 idx hcount
          calc
            Succinct.select false
                (Cartesian.CartesianShape.node left right).bpCode idx =
              Succinct.selectFrom false
                (left.bpCode ++ false :: right.bpCode) 1 idx := by
                simp [Cartesian.CartesianShape.bpCode, Succinct.select,
                  Succinct.selectFrom]
            _ = Succinct.selectFrom false (false :: right.bpCode)
                (1 + left.bpCode.length) (idx - left.size) := by
                simpa [bpCode_rankFalse_full left] using hdrop
            _ = some (left.bpCode.length + 1) := by
                simp [Succinct.selectFrom, hroot]
                omega
            _ = bpCloseOfInorder?
                (Cartesian.CartesianShape.node left right) idx := by
                simp [bpCloseOfInorder?, hroot]
        · have hcount :
              Succinct.rankPrefix false left.bpCode left.bpCode.length <=
                idx := by
            rw [bpCode_rankFalse_full left]
            omega
          have hdrop :=
            Succinct.selectFrom_append_right_after_count false
              left.bpCode (false :: right.bpCode) 1 idx hcount
          have hdrop' :
              Succinct.selectFrom false
                  (left.bpCode ++ false :: right.bpCode) 1 idx =
                Succinct.selectFrom false (false :: right.bpCode)
                  (1 + left.bpCode.length) (idx - left.size) := by
            simpa [bpCode_rankFalse_full left] using hdrop
          have hocc : idx - left.size ≠ 0 := by
            omega
          have htail :
              Succinct.selectFrom false (false :: right.bpCode)
                  (1 + left.bpCode.length) (idx - left.size) =
                Succinct.selectFrom false right.bpCode
                  (left.bpCode.length + 2) (idx - left.size - 1) := by
            have hbase :
                1 + left.bpCode.length + 1 = left.bpCode.length + 2 := by
              omega
            simp [Succinct.selectFrom, hocc, hbase]
          have hbaseSelect :=
            Succinct.selectFrom_base_eq false right.bpCode
              (left.bpCode.length + 2) (idx - left.size - 1)
          calc
            Succinct.select false
                (Cartesian.CartesianShape.node left right).bpCode idx =
              Succinct.selectFrom false
                (left.bpCode ++ false :: right.bpCode) 1 idx := by
                simp [Cartesian.CartesianShape.bpCode, Succinct.select,
                  Succinct.selectFrom]
            _ = Succinct.selectFrom false (false :: right.bpCode)
                (1 + left.bpCode.length) (idx - left.size) := by
                exact hdrop'
            _ = Succinct.selectFrom false right.bpCode
                (left.bpCode.length + 2) (idx - left.size - 1) := htail
            _ = (Succinct.select false right.bpCode
                (idx - left.size - 1)).map
                  (fun pos => left.bpCode.length + 2 + pos) := hbaseSelect
            _ = (bpCloseOfInorder? right (idx - left.size - 1)).map
                  (fun pos => left.bpCode.length + 2 + pos) := by
                rw [ihright]
            _ = bpCloseOfInorder?
                (Cartesian.CartesianShape.node left right) idx := by
                simp [bpCloseOfInorder?, hleft, hroot]

end SuccinctSpace

end RMQ

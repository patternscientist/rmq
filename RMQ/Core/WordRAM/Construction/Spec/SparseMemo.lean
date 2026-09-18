import RMQ.Core.WordRAM.Construction.Spec.BlockStats
import RMQ.Core.WordRAM.Construction.Spec.ArgMinSplit

/-!
# PRE-1 S4: the sparse memos as reference identities

Machine-free specification layer (outside the builder firewall). The builder
selects between two blocks by comparing their stored minimum excess; the
reference `bpBetterArgMinBlock` compares the excess at their leftmost argmin
positions. `argPos_excess_eq_min` identifies the two keys for every block
inside the covered range, so `better_eq_min` restates the reference selection
with the stored keys. `rangeArgMin_snoc` is the one-candidate extension used by
the macro scan, and `globalMemo_double` the macro-granularity doubling law in
the index form the global memo uses.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.SuccinctClose

/-- The argmin prefix of `k + 1` samples attains the minimum of those samples. -/
theorem argAcc_excess_eq_min (shape : CartesianShape) (start : Nat) :
    ∀ k, start + k ≤ shape.bpCode.length →
      bpExcessAt shape (argAcc shape start (k + 1) start) =
        natListMinFrom shape.bpCode.length
          ((List.range (k + 1)).map (fun off => bpExcessAt shape (start + off)))
  | 0, h => by
      have hmin : Nat.min start shape.bpCode.length = start := Nat.min_eq_left (by omega)
      have hle := bpExcessAt_le_length shape start
      show bpExcessAt shape (argStep shape (start + 0) start) =
        Nat.min shape.bpCode.length (bpExcessAt shape (start + 0))
      unfold argStep
      rw [Nat.add_zero, hmin, if_neg (Nat.lt_irrefl _)]
      exact (Nat.min_eq_right hle).symm
  | k + 1, h => by
      have ih := argAcc_excess_eq_min shape start k (by omega)
      have hmin : Nat.min (start + (k + 1)) shape.bpCode.length = start + (k + 1) :=
        Nat.min_eq_left h
      rw [range_map_succ, natListMinFrom_append_singleton, ← ih]
      show bpExcessAt shape (argStep shape (start + (k + 1)) (argAcc shape start (k + 1) start)) = _
      unfold argStep
      rw [hmin]
      by_cases hlt : bpExcessAt shape (start + (k + 1)) <
          bpExcessAt shape (argAcc shape start (k + 1) start)
      · rw [if_pos hlt]; exact (Nat.min_eq_right (Nat.le_of_lt hlt)).symm
      · rw [if_neg hlt]; exact (Nat.min_eq_left (Nat.le_of_not_lt hlt)).symm

/-- **Stored key.** Inside the covered range, the excess at a block's leftmost
argmin position is its minimum sampled excess. -/
theorem argPos_excess_eq_min (shape : CartesianShape) (bs b : Nat)
    (hb : b * bs + bs ≤ shape.bpCode.length) :
    bpExcessAt shape (bpBlockArgMinPrefixPos shape bs b) = bpBlockMinExcess shape bs b := by
  have hmin : Nat.min (b * bs) shape.bpCode.length = b * bs := Nat.min_eq_left (by omega)
  show bpExcessAt shape (bpBlockArgMinPrefixPosFrom shape (blockStartOf bs b) (bs + 1)
      (Nat.min (blockStartOf bs b) shape.bpCode.length)) = _
  rw [show blockStartOf bs b = b * bs from rfl, hmin, bpBlockArgMinPrefixPosFrom_eq_argAcc,
    argAcc_excess_eq_min shape (b * bs) bs hb]
  rfl

/-- **Selection by stored keys.** -/
theorem better_eq_min (shape : CartesianShape) (bs x y : Nat)
    (hx : x * bs + bs ≤ shape.bpCode.length) (hy : y * bs + bs ≤ shape.bpCode.length) :
    bpBetterArgMinBlock shape bs x y =
      if bpBlockMinExcess shape bs y < bpBlockMinExcess shape bs x then y else x := by
  unfold bpBetterArgMinBlock
  rw [argPos_excess_eq_min shape bs x hx, argPos_excess_eq_min shape bs y hy]

/-- The fold over `k + 1` candidates extends the fold over `k` by one selection. -/
theorem rangeArgMin_snoc (shape : CartesianShape) (bs st k : Nat) :
    bpRangeArgMinBlock shape bs st (k + 2) =
      bpBetterArgMinBlock shape bs (bpRangeArgMinBlock shape bs st (k + 1)) (st + 1 + k) := by
  show bpRangeArgMinBlockFrom shape bs (st + 1) (k + 1) st =
    bpBetterArgMinBlock shape bs (bpRangeArgMinBlockFrom shape bs (st + 1) k st) (st + 1 + k)
  rw [bpRangeArgMinBlockFrom_add shape bs (st + 1) k 1 st]
  rfl

/-- Macro-granularity doubling in the memo's index form. -/
theorem globalMemo_double (shape : CartesianShape) (bs M m l : Nat) :
    bpRangeArgMinBlock shape bs (m * M) (2 ^ (l + 1) * M) =
      bpBetterArgMinBlock shape bs
        (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))
        (bpRangeArgMinBlock shape bs ((m + 2 ^ l) * M) (2 ^ l * M)) := by
  rw [bpRangeArgMinBlock_pow_succ_mul, Nat.add_mul]

/-- Local doubling in the memo's index form. -/
theorem localMemo_double (shape : CartesianShape) (bs b l : Nat) :
    bpRangeArgMinBlock shape bs (b * 1) (2 ^ (l + 1) * 1) =
      bpBetterArgMinBlock shape bs
        (bpRangeArgMinBlock shape bs (b * 1) (2 ^ l * 1))
        (bpRangeArgMinBlock shape bs ((b + 2 ^ l) * 1) (2 ^ l * 1)) :=
  globalMemo_double shape bs 1 b l

end RMQ.SuccinctFinal.PackedConstruction.Spec

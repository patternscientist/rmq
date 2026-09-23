import RMQ.Core.WordRAM.Construction.Spec.Dyck
import RMQ.Core.SuccinctClose.RelativeSummary

/-!
# PRE-1 S4: block statistics as left folds

Machine-free specification layer (outside the builder firewall). The reference
block statistics are list functions over the `blockSize + 1` excess samples of a
block and a tail-recursive argmin. The builder folds the samples one at a time,
so this module restates them as left folds: `natListMinFrom_append_singleton`,
`natListMax_append_singleton`, `samples_take_succ` and `argAcc` with
`bpBlockArgMinPrefixPosFrom_eq_argAcc`. It also records the excess recurrence
on a BP cell (`excess_step`) and the two non-underflow facts the relative
entries need.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian SuccinctClose

theorem natListMinFrom_append_singleton (seed : Nat) :
    ∀ (L : List Nat) (x : Nat), natListMinFrom seed (L ++ [x]) = Nat.min (natListMinFrom seed L) x
  | [], x => rfl
  | a :: L, x => by
      show natListMinFrom (Nat.min seed a) (L ++ [x]) = Nat.min (natListMinFrom (Nat.min seed a) L) x
      exact natListMinFrom_append_singleton (Nat.min seed a) L x

theorem natListMax_append_singleton : ∀ (L : List Nat) (x : Nat),
    natListMax (L ++ [x]) = Nat.max (natListMax L) x
  | [], x => by simp [natListMax]
  | a :: L, x => by
      show Nat.max a (natListMax (L ++ [x])) = Nat.max (Nat.max a (natListMax L)) x
      rw [natListMax_append_singleton L x]
      generalize natListMax L = m
      show max a (max m x) = max (max a m) x
      omega

theorem samples_take (shape : CartesianShape) (blockSize block k : Nat) (hk : k ≤ blockSize + 1) :
    (bpBlockExcessSamples shape blockSize block).take k =
      (List.range k).map (fun offset => bpExcessAt shape (blockStartOf blockSize block + offset)) := by
  unfold bpBlockExcessSamples
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

theorem range_map_succ (f : Nat → Nat) (k : Nat) :
    (List.range (k + 1)).map f = (List.range k).map f ++ [f k] := by
  rw [List.range_succ, List.map_append]
  rfl

/-- One argmin step at position `p`. -/
def argStep (shape : CartesianShape) (p best : Nat) : Nat :=
  if bpExcessAt shape (Nat.min p shape.bpCode.length) < bpExcessAt shape best then
    Nat.min p shape.bpCode.length else best

/-- The best position after `k` argmin steps starting at `pos`. -/
def argAcc (shape : CartesianShape) (pos : Nat) : Nat → Nat → Nat
  | 0, best => best
  | k + 1, best => argStep shape (pos + k) (argAcc shape pos k best)

theorem argAcc_shift (shape : CartesianShape) (pos : Nat) :
    ∀ (k best : Nat), argAcc shape pos (k + 1) best = argAcc shape (pos + 1) k (argStep shape pos best)
  | 0, best => rfl
  | k + 1, best => by
      show argStep shape (pos + (k + 1)) (argAcc shape pos (k + 1) best) =
        argStep shape (pos + 1 + k) (argAcc shape (pos + 1) k (argStep shape pos best))
      rw [argAcc_shift shape pos k best, show pos + (k + 1) = pos + 1 + k by omega]

theorem bpBlockArgMinPrefixPosFrom_eq_argAcc (shape : CartesianShape) :
    ∀ (steps pos best : Nat),
      bpBlockArgMinPrefixPosFrom shape pos steps best = argAcc shape pos steps best
  | 0, pos, best => rfl
  | steps + 1, pos, best => by
      rw [argAcc_shift]
      show bpBlockArgMinPrefixPosFrom shape (pos + 1) steps (argStep shape pos best) = _
      exact bpBlockArgMinPrefixPosFrom_eq_argAcc shape steps (pos + 1) (argStep shape pos best)

/-- The excess recurrence on one BP cell, as the builder computes it. -/
theorem excess_step (shape : CartesianShape) {p : Nat} (hp : p < shape.bpCode.length) :
    (shape.bpCode[p] = true →
      bpExcessAt shape (p + 1) = bpExcessAt shape p + 1) ∧
    (shape.bpCode[p] = false →
      1 ≤ bpExcessAt shape p ∧ bpExcessAt shape (p + 1) = bpExcessAt shape p - 1) := by
  refine ⟨fun h => bpExcessAt_succ_of_open shape (by simp [List.getElem?_eq_getElem hp, h]),
    fun h => bpExcessAt_succ_of_close shape (by simp [List.getElem?_eq_getElem hp, h])⟩

/-- The argmin position of a block never precedes the block start. -/
theorem argAcc_ge (shape : CartesianShape) (start : Nat) (hlimit : start ≤ shape.bpCode.length) :
    ∀ (k : Nat), start ≤ argAcc shape start k start
  | 0 => Nat.le_refl _
  | k + 1 => by
      show start ≤ argStep shape (start + k) (argAcc shape start k start)
      have ih := argAcc_ge shape start hlimit k
      unfold argStep
      split
      · have : start ≤ Nat.min (start + k) shape.bpCode.length := by
          simp only [Nat.min_def]; split <;> omega
        exact this
      · exact ih

end RMQ.SuccinctFinal.PackedConstruction.Spec

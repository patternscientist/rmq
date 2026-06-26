/-!
# Small List lemmas

This module collects tiny Mathlib-free List facts that are reused across the
core proof layers.
-/

namespace RMQ

theorem sum_map_const_nat {alpha : Type u} (xs : List alpha) (n : Nat) :
    ((xs.map fun _ => n).sum) = xs.length * n := by
  simp [List.map_const']

end RMQ

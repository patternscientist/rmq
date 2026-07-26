import RMQ.Core.SuccinctFinal.RAM.GeometryClosure

/-! Anti-vacuity for the footprint hypothesis: it genuinely admits stores that
differ. Otherwise the composite would be no stronger than whole-store sharing. -/

open RMQ

namespace C06AV

/-- `store` with one address overwritten. -/
def upd (store : WordRAM.ReadStore) (s i : Nat) (w : Option WordRAM.Word) :
    WordRAM.ReadStore where
  readWord? := fun seg idx => if seg = s ∧ idx = i then w else store.readWord? seg idx

/-- Overwriting any address OUTSIDE the ordered read footprint preserves
footprint agreement. The hypothesis is therefore satisfied by stores that
differ, at every address the execution does not probe. -/
theorem agree_off_footprint
    (xs : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (s i : Nat) (w : Option WordRAM.Word)
    (hnot : (s, i) ∉ SuccinctClassic.orderedReadFootprintWithStore xs store l r) :
    SuccinctClassic.storesAgreeOnOrderedReadFootprint xs store (upd store s i w) l r := by
  intro seg idx hmem
  by_cases h : seg = s ∧ idx = i
  · exfalso
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact hnot hmem
  · simp [upd, h]

/-- The composite therefore applies to two genuinely different stores. -/
theorem composite_applies_off_diagonal
    (xs ys : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (s i : Nat) (w : Option WordRAM.Word)
    (hlen : xs.length = ys.length)
    (hnot : (s, i) ∉ SuccinctClassic.orderedReadFootprintWithStore xs store l r) :
    SuccinctClassic.queryTraceResultWithStore xs store l r =
      SuccinctClassic.queryTraceResultWithStore ys (upd store s i w) l r :=
  SuccinctFinal.GeometryClosure.queryTraceResultWithStore_length_and_footprint
    xs ys store (upd store s i w) l r hlen (agree_off_footprint xs store l r s i w hnot)

/-- And the two stores really are different functions when the overwrite
changes the value there. -/
example (store : WordRAM.ReadStore) (s i : Nat) (w : Option WordRAM.Word)
    (hne : store.readWord? s i ≠ w) : upd store s i w ≠ store := by
  intro hEq
  apply hne
  have := congrArg (fun t => WordRAM.ReadStore.readWord? t s i) hEq
  simpa [upd] using this.symm

#print axioms agree_off_footprint
#print axioms composite_applies_off_diagonal

end C06AV

import RMQ.Core.WordRAM.Construction.Spec.OpenCounts

/-!
# PRE-1 S3: the right spine of the stack Cartesian tree

Machine-free specification layer (outside the builder firewall). The monotone
stack of the builder holds, bottom to top, the right spine of the Cartesian tree
of the processed prefix. `spineFrom t o` lists that spine root first, for the
tree `t` placed at inorder offset `o`, as triples

`(inorder index of the node, inorder index of the leftmost node of its subtree, value)`.

`spineFrom_insertRight` states what one right-end insertion does to the spine:
the prefix of nodes whose value is not strictly larger than the new value is
kept, and the new node is appended with the leftmost index of the first node
that is strictly larger (the moved subtree), or its own index if there is none.
`insertPoint_eq_find` identifies the reference `insertPoint` with that first
node. `spineFrom_sorted` (spine values are non-decreasing for a valid tree) and
`takeWhile_find_of_split` turn the builder's pop-from-the-top loop into the
reference's descend-from-the-root recursion. These are reference-side lemmas;
the charged builder never calls `spineFrom` or `insertRight`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian

namespace StackCartesianTreeSpec

open StackCartesianTree

/-- The right spine of `t` at inorder offset `o`, root first. -/
def spineFrom : StackCartesianTree → Nat → List (Nat × Nat × Int)
  | .empty, _ => []
  | .node left v right, o =>
      (o + left.shape.size, o, v) :: spineFrom right (o + left.shape.size + 1)

/-- The builder's pop predicate on a spine entry. -/
def popsFor (v : Int) (e : Nat × Nat × Int) : Bool := decide (v < e.2.2)

theorem values_length (t : StackCartesianTree) : t.values.length = t.shape.size := by
  induction t with
  | empty => rfl
  | node l v r ihl ihr =>
      simp only [values, StackCartesianTree.shape, CartesianShape.size, List.length_append,
        List.length_cons, ihl, ihr]
      omega

/-- **Spine after insertion.** -/
theorem spineFrom_insertRight (t : StackCartesianTree) (v : Int) (o : Nat) :
    spineFrom (t.insertRight v) o =
      (spineFrom t o).takeWhile (fun e => !popsFor v e) ++
        [(o + t.shape.size, ((spineFrom t o).find? (popsFor v)).elim (o + t.shape.size) (·.2.1),
          v)] := by
  induction t generalizing o with
  | empty => simp [insertRight, spineFrom, StackCartesianTree.shape, CartesianShape.size]
  | node l p r _ihl ihr =>
      by_cases hvp : v < p
      · simp [insertRight, hvp, spineFrom, popsFor, StackCartesianTree.shape,
          CartesianShape.size]
      · have hnp : popsFor v (o + l.shape.size, o, p) = false := by simp [popsFor, hvp]
        simp only [insertRight, hvp, if_false, spineFrom]
        rw [ihr (o + l.shape.size + 1), List.takeWhile_cons, List.find?_cons, hnp]
        simp only [Bool.not_false, if_true, List.cons_append, StackCartesianTree.shape,
          CartesianShape.size]
        rw [show o + l.shape.size + 1 + r.shape.size = o + (l.shape.size + 1 + r.shape.size) by
          omega]

/-- **Insertion point.** The reference insertion point is the leftmost index of
the first spine node whose value is strictly larger than the new value. -/
theorem insertPoint_eq_find (t : StackCartesianTree) (v : Int) (o : Nat) :
    (insertPoint t v).map (o + ·) = ((spineFrom t o).find? (popsFor v)).map (·.2.1) := by
  induction t generalizing o with
  | empty => rfl
  | node l p r _ihl ihr =>
      by_cases hvp : v < p
      · simp [insertPoint, hvp, spineFrom, popsFor]
      · have hnp : popsFor v (o + l.shape.size, o, p) = false := by simp [popsFor, hvp]
        simp only [insertPoint, hvp, if_false, spineFrom, List.find?_cons, hnp]
        rw [← ihr (o + l.shape.size + 1), Option.map_map]
        congr 1
        funext k
        simp only [Function.comp]
        omega

/-- Spine entries: offsets, leftmost indices and values. -/
theorem spineFrom_mem (t : StackCartesianTree) (o : Nat) :
    ∀ e ∈ spineFrom t o, o ≤ e.2.1 ∧ e.2.1 ≤ e.1 ∧ e.1 < o + t.shape.size ∧
      t.values[e.1 - o]? = some e.2.2 ∧ e.2.2 ∈ t.values := by
  induction t generalizing o with
  | empty => simp [spineFrom]
  | node l p r _ihl ihr =>
      intro e he
      simp only [spineFrom, List.mem_cons] at he
      have hlen := values_length l
      rcases he with rfl | he
      · refine ⟨Nat.le_refl _, by simp, ?_, ?_, ?_⟩
        · simp [StackCartesianTree.shape, CartesianShape.size]; omega
        · simp only [values, Nat.add_sub_cancel_left]
          rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          rfl
        · simp [values]
      · obtain ⟨h1, h2, h3, h4, h5⟩ := ihr _ e he
        refine ⟨by omega, h2, ?_, ?_, ?_⟩
        · simp only [StackCartesianTree.shape, CartesianShape.size]; omega
        · simp only [values]
          rw [List.getElem?_append_right (by omega), hlen]
          have : e.1 - o - l.shape.size = (e.1 - (o + l.shape.size + 1)) + 1 := by omega
          rw [this, List.getElem?_cons_succ]
          exact h4
        · simp [values, h5]

/-- **Sorted spine.** Along the right spine of a valid tree, values never decrease. -/
theorem spineFrom_sorted {t : StackCartesianTree} (hv : t.Valid) (o : Nat) :
    (spineFrom t o).Pairwise (fun a b => a.2.2 ≤ b.2.2) := by
  induction t generalizing o with
  | empty => simp [spineFrom]
  | node l p r _ihl ihr =>
      obtain ⟨_, hvr, _, hright⟩ := hv
      simp only [spineFrom, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ihr hvr _⟩
      exact hright _ (spineFrom_mem r _ b hb).2.2.2.2

/-- A list split at `sp` into a prefix where `p` fails and a suffix where it holds. -/
theorem takeWhile_find_of_split {α : Type} (p : α → Bool) :
    ∀ (L : List α) (sp : Nat),
      (∀ k (hk : k < L.length), k < sp → p L[k] = false) →
      (∀ k (hk : k < L.length), sp ≤ k → p L[k] = true) →
      L.takeWhile (fun e => !p e) = L.take sp ∧ L.find? p = L[sp]?
  | [], _, _, _ => by simp
  | a :: L, 0, _, h2 => by
      have ha : p a = true := h2 0 (by simp) (Nat.le_refl _)
      simp [ha]
  | a :: L, sp + 1, h1, h2 => by
      have ha : p a = false := h1 0 (by simp) (by omega)
      obtain ⟨ht, hf⟩ := takeWhile_find_of_split p L sp
        (fun k hk hks => h1 (k + 1) (by simp; omega) (by omega))
        (fun k hk hks => h2 (k + 1) (by simp; omega) (by omega))
      simp [ha, ht, hf]

theorem sum_append_nat : ∀ (L M : List Nat), (L ++ M).sum = L.sum + M.sum
  | [], M => by simp
  | a :: L, M => by simp [sum_append_nat L M]; omega

/-- The open counts sum to the number of nodes. -/
theorem openCounts_sum (T : CartesianShape) : (openCounts T).sum = T.size := by
  induction T with
  | empty => rfl
  | node l r ihl ihr =>
      rw [openCounts_node, sum_append_nat]
      cases h : openCounts l with
      | nil =>
          rw [h] at ihl
          simp [CartesianShape.size, ← ihl, ihr]
      | cons a L =>
          rw [h] at ihl
          simp only [List.cons_append, List.modifyHead_cons, List.sum_cons, sum_append_nat,
            CartesianShape.size, ← ihl, ← ihr]
          simp
          omega

theorem le_sum_of_mem {L : List Nat} {c : Nat} (h : c ∈ L) : c ≤ L.sum := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
      simp only [List.mem_cons] at h
      simp only [List.sum_cons]
      rcases h with rfl | h
      · omega
      · have := ih h; omega

theorem getD_of_lt {L : List Nat} {j : Nat} (h : j < L.length) : L.getD j 0 = L[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_of_ge {L : List Nat} {j : Nat} (h : L.length ≤ j) : L.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem openCounts_getD_le (T : CartesianShape) (j : Nat) :
    (openCounts T).getD j 0 ≤ T.size := by
  rw [← openCounts_sum]
  by_cases hj : j < (openCounts T).length
  · rw [getD_of_lt hj]
    exact le_sum_of_mem (List.getElem_mem hj)
  · rw [getD_of_ge (by omega)]; omega

theorem getD_append_singleton (L : List Nat) (a j : Nat) :
    (L ++ [a]).getD j 0 = if j < L.length then L.getD j 0 else if j = L.length then a else 0 := by
  by_cases h1 : j < L.length
  · rw [if_pos h1, getD_of_lt (by simp; omega), getD_of_lt h1, List.getElem_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : j = L.length
    · subst h2; simp [List.getD_eq_getElem?_getD]
    · rw [if_neg h2, getD_of_ge (by simp; omega)]

theorem getD_modify_succ (L : List Nat) (k j : Nat) (hk : k < L.length) :
    (L.modify k (· + 1)).getD j 0 = if j = k then L.getD k 0 + 1 else L.getD j 0 := by
  by_cases hj : j < L.length
  · rw [getD_of_lt (by simp; omega), List.getElem_modify]
    by_cases hjk : j = k
    · subst hjk; simp [List.getElem?_eq_getElem hj]
    · simp [hjk, Ne.symm hjk, List.getElem?_eq_getElem hj]
  · rw [getD_of_ge (by simp; omega), if_neg (by omega), getD_of_ge (by omega)]

theorem take_succ_getD {xs : List Int} {i : Nat} (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs.getD i 0] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem buildTree_take_size (xs : List Int) (i : Nat) (hi : i ≤ xs.length) :
    (buildTree (xs.take i)).shape.size = i := by
  rw [← values_length, buildTree_values, List.length_take]
  omega

theorem spine_entry_facts (xs : List Int) (i : Nat) (hi : i ≤ xs.length) :
    ∀ e ∈ spineFrom (buildTree (xs.take i)) 0, e.2.1 ≤ e.1 ∧ e.1 < i ∧ xs.getD e.1 0 = e.2.2 := by
  intro e he
  obtain ⟨_, h2, h3, h4, _⟩ := spineFrom_mem _ 0 e he
  rw [buildTree_take_size xs i hi] at h3
  rw [buildTree_values, Nat.sub_zero, List.getElem?_take] at h4
  simp only [Nat.zero_add] at h3
  rw [if_pos h3] at h4
  refine ⟨h2, h3, ?_⟩
  simp [List.getD, h4]

end StackCartesianTreeSpec

end RMQ.SuccinctFinal.PackedConstruction.Spec

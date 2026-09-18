import RMQ.Core.Shape

/-!
# PRE-1 S1: open counts of a Cartesian shape

Machine-free specification layer (outside the builder firewall; nothing in the
operational closure imports it). The balanced-parentheses code of a Cartesian
shape emits, for every node in inorder, a run of opening bits followed by that
node's closing bit. `openCounts T` lists those run lengths in inorder, so

`T.bpCode = (openCounts T).flatMap (fun c => List.replicate c true ++ [false])`.

The monotone-stack builder never materializes the tree: inserting a value at
the right end either appends a new node with count 1 (the value descends past
the whole right spine) or moves a right-spine subtree under the new node, which
adds one opening bit in front of that subtree's leftmost node and appends a
count-0 entry. `openCounts_insertRight` states exactly this, with the strict
`value < pivot` pop test of the reference `insertRight` (equal keys descend
right, so ties stay leftmost).

These are reference-side lemmas only: the charged builder never calls
`openCounts`, `insertRight` or `bpCode`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian

/-- Inorder run lengths of opening bits in the BP code. The head of the left
part is bumped because the node's own opening bit precedes its left subtree. -/
def openCounts : CartesianShape → List Nat
  | .empty => []
  | .node left right =>
      (openCounts left ++ [0]).modifyHead (· + 1) ++ openCounts right

/-- One inorder unit of the BP code: `c` opening bits, then one closing bit. -/
def bpUnit (c : Nat) : List Bool :=
  List.replicate c true ++ [false]

@[simp] theorem openCounts_empty : openCounts .empty = [] := rfl

theorem openCounts_node (left right : CartesianShape) :
    openCounts (.node left right) =
      (openCounts left ++ [0]).modifyHead (· + 1) ++ openCounts right := rfl

/-- The length law: one entry per node. -/
theorem openCounts_length (T : CartesianShape) :
    (openCounts T).length = T.size := by
  induction T with
  | empty => rfl
  | node left right ihl ihr =>
      simp only [openCounts_node, List.length_append, List.length_modifyHead,
        List.length_singleton, ihl, ihr, CartesianShape.size]

theorem modifyHead_succ_append_ne_nil {L : List Nat} (h : L ≠ []) (M : List Nat) :
    (L ++ M).modifyHead (· + 1) = L.modifyHead (· + 1) ++ M := by
  cases L with
  | nil => exact absurd rfl h
  | cons a L => rfl

theorem flatMap_bpUnit_modifyHead_succ {L : List Nat} (h : L ≠ []) :
    (L.modifyHead (· + 1)).flatMap bpUnit = true :: L.flatMap bpUnit := by
  cases L with
  | nil => exact absurd rfl h
  | cons a L =>
      simp [bpUnit, List.replicate_succ]

/-- **BP law.** The BP code is the concatenation of the inorder units. -/
theorem bpCode_eq_openCounts_flatMap (T : CartesianShape) :
    T.bpCode = (openCounts T).flatMap (fun c => List.replicate c true ++ [false]) := by
  change T.bpCode = (openCounts T).flatMap bpUnit
  induction T with
  | empty => rfl
  | node left right ihl ihr =>
      have hne : openCounts left ++ [0] ≠ [] := by simp
      rw [openCounts_node, List.flatMap_append, flatMap_bpUnit_modifyHead_succ hne,
        List.flatMap_append, ← ihl, ← ihr]
      simp [CartesianShape.bpCode, bpUnit]

theorem openCounts_ne_nil_of_node (left right : CartesianShape) :
    openCounts (.node left right) ≠ [] := by
  rw [openCounts_node]
  cases h : openCounts left <;> simp

theorem modify_append_length {α : Type} (f : α → α) :
    ∀ (L M : List α) (k : Nat), (L ++ M).modify (L.length + k) f = L ++ M.modify k f
  | [], M, k => by simp
  | a :: L, M, k => by
      have ih := modify_append_length f L M k
      rw [List.length_cons, Nat.add_right_comm, List.cons_append, List.modify_succ_cons, ih,
        List.cons_append]

namespace StackCartesianTreeSpec

open StackCartesianTree

/-- The inorder index, inside `t`, of the leftmost node of the right-spine
subtree that `t.insertRight value` moves under the new node: the first spine
node from the root whose pivot is strictly larger than `value`. `none` when the
value descends past the whole right spine. -/
def insertPoint : StackCartesianTree → Int → Option Nat
  | .empty, _ => none
  | .node left pivot right, value =>
      if value < pivot then some 0
      else (insertPoint right value).map (fun k => left.shape.size + 1 + k)

/-- **Insertion law.** Right-end insertion either appends a count-1 unit or
adds one opening bit at the leftmost node of the moved spine subtree and
appends a count-0 unit. -/
theorem openCounts_insertRight (t : StackCartesianTree) (value : Int) :
    openCounts (t.insertRight value).shape =
      match insertPoint t value with
      | none => openCounts t.shape ++ [1]
      | some ld => (openCounts t.shape).modify ld (· + 1) ++ [0] := by
  induction t with
  | empty => rfl
  | node left pivot right _ihl ihr =>
      by_cases hlt : value < pivot
      · have hne := openCounts_ne_nil_of_node left.shape right.shape
        simp only [insertRight, hlt, if_true, insertPoint, StackCartesianTree.shape]
        rw [openCounts_node (.node left.shape right.shape) .empty,
          modifyHead_succ_append_ne_nil hne, List.modifyHead_eq_modify_zero]
        simp
      · simp only [insertRight, hlt, if_false, insertPoint, StackCartesianTree.shape]
        rw [openCounts_node, ihr, openCounts_node]
        cases hp : insertPoint right value with
        | none => simp [List.append_assoc]
        | some k =>
            simp only [Option.map_some]
            have hlen : ((openCounts left.shape ++ [0]).modifyHead (· + 1)).length =
                left.shape.size + 1 := by
              simp [openCounts_length]
            rw [← hlen, modify_append_length, List.append_assoc]

theorem buildTreeAux_append_singleton (tree : StackCartesianTree) (xs : List Int)
    (value : Int) :
    buildTreeAux tree (xs ++ [value]) = (buildTreeAux tree xs).insertRight value := by
  induction xs generalizing tree with
  | nil => simp [buildTreeAux, insertRightStack_eq_insertRight]
  | cons x xs ih => simp [buildTreeAux, ih]

theorem buildTree_append_singleton (xs : List Int) (value : Int) :
    buildTree (xs ++ [value]) = (buildTree xs).insertRight value :=
  buildTreeAux_append_singleton _ xs value

@[simp] theorem buildTree_nil : buildTree [] = .empty := rfl

/-- The canonical Cartesian shape of any list is the stack tree's shape. -/
theorem shape_eq_buildTree_shape (xs : List Int) :
    Cartesian.shape xs = (buildTree xs).shape :=
  (stackCartesianShape_eq_shape xs).symm

/-- The BP code of the canonical shape of `xs`, through the stack tree. -/
theorem bpCode_shape_eq_openCounts_buildTree (xs : List Int) :
    (Cartesian.shape xs).bpCode =
      (openCounts (buildTree xs).shape).flatMap
        (fun c => List.replicate c true ++ [false]) := by
  rw [shape_eq_buildTree_shape, bpCode_eq_openCounts_flatMap]

end StackCartesianTreeSpec

end RMQ.SuccinctFinal.PackedConstruction.Spec

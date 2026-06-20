import RMQ.Core.Backend

/-!
# LCA-facing Euler traces

This module starts the correctness-first bridge from RMQ to LCA. It introduces
a small rose-tree model, proves the Euler-depth plus/minus-one invariant for generated
depth traces, and packages the RMQ-backed "minimum-depth tour node between two
first occurrences" reduction.
-/

namespace RMQ

/-- A tiny proof-friendly rooted tree with natural-number node labels. -/
inductive RoseTree where
  | node (label : Nat) (children : List RoseTree)
deriving Repr

namespace RoseTree

mutual
  /--
  Euler-tour depth moves for a tree. A child descent contributes `+1`, and the
  corresponding return to the parent contributes `-1`.
  -/
  def eulerMoves : RoseTree -> List Int
    | node _ children => eulerMovesForest children

  /-- Euler-tour depth moves for a forest of children. -/
  def eulerMovesForest : List RoseTree -> List Int
    | [] => []
    | child :: rest => 1 :: (eulerMoves child ++ (-1) :: eulerMovesForest rest)
end

mutual
  /-- Euler-tour node labels for a tree. -/
  def eulerNodes : RoseTree -> List Nat
    | node label children => label :: eulerNodesForest label children

  /-- Euler-tour node labels for a forest of children, returning to `parent`. -/
  def eulerNodesForest (parent : Nat) : List RoseTree -> List Nat
    | [] => []
    | child :: rest => eulerNodes child ++ parent :: eulerNodesForest parent rest
end

end RoseTree

/-- A depth move is one Euler step up or down. -/
def UnitDepthMove (move : Int) : Prop :=
  move = 1 \/ move = -1

/-- Every move in a list is an Euler unit step. -/
def UnitDepthMoves : List Int -> Prop
  | [] => True
  | move :: rest => UnitDepthMove move /\ UnitDepthMoves rest

theorem unitDepthMoves_append {xs ys : List Int} :
    UnitDepthMoves (xs ++ ys) <-> UnitDepthMoves xs /\ UnitDepthMoves ys := by
  induction xs with
  | nil =>
      simp [UnitDepthMoves]
  | cons move rest ih =>
      simp [UnitDepthMoves, ih, and_assoc]

mutual
  theorem roseTree_eulerMoves_unit (tree : RoseTree) :
      UnitDepthMoves tree.eulerMoves := by
    cases tree with
    | node _ children =>
        simpa [RoseTree.eulerMoves] using roseTree_eulerMovesForest_unit children

  theorem roseTree_eulerMovesForest_unit (forest : List RoseTree) :
      UnitDepthMoves (RoseTree.eulerMovesForest forest) := by
    cases forest with
    | nil =>
        simp [RoseTree.eulerMovesForest, UnitDepthMoves]
    | cons child rest =>
        have hchild : UnitDepthMoves child.eulerMoves :=
          roseTree_eulerMoves_unit child
        have hrest : UnitDepthMoves (RoseTree.eulerMovesForest rest) :=
          roseTree_eulerMovesForest_unit rest
        simp [RoseTree.eulerMovesForest, UnitDepthMoves, unitDepthMoves_append,
          hchild, hrest, UnitDepthMove]
end

/--
Depths obtained by starting at `start` and applying a list of Euler depth moves.
The result always includes the starting depth.
-/
def depthsFromMoves (start : Int) : List Int -> List Int
  | [] => [start]
  | move :: rest => start :: depthsFromMoves (start + move) rest

/-- Final depth reached after applying a list of Euler moves. -/
def depthAfterMoves (start : Int) : List Int -> Int
  | [] => start
  | move :: rest => depthAfterMoves (start + move) rest

theorem depthAfterMoves_append
    (start : Int) (xs ys : List Int) :
    depthAfterMoves start (xs ++ ys) =
      depthAfterMoves (depthAfterMoves start xs) ys := by
  induction xs generalizing start with
  | nil =>
      simp [depthAfterMoves]
  | cons move rest ih =>
      simp [depthAfterMoves, ih]

theorem depthsFromMoves_append_cons
    (start : Int) (xs : List Int) (move : Int) (ys : List Int) :
    depthsFromMoves start (xs ++ move :: ys) =
      depthsFromMoves start xs ++
        depthsFromMoves (depthAfterMoves start xs + move) ys := by
  induction xs generalizing start with
  | nil =>
      simp [depthsFromMoves, depthAfterMoves]
  | cons head tail ih =>
      simp [depthsFromMoves, depthAfterMoves, ih]

/-- Adjacent depth values differ by exactly one. -/
def AdjacentDepthsDifferByOne : List Int -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (b = a + 1 \/ a = b + 1) /\ AdjacentDepthsDifferByOne (b :: rest)

theorem unitDepthMove_step (depth move : Int)
    (hmove : UnitDepthMove move) :
    (depth + move = depth + 1 \/ depth = depth + move + 1) := by
  rcases hmove with hmove | hmove
  · left
    omega
  · right
    omega

theorem depthsFromMoves_adjacent
    (start : Int) {moves : List Int}
    (hmoves : UnitDepthMoves moves) :
    AdjacentDepthsDifferByOne (depthsFromMoves start moves) := by
  induction moves generalizing start with
  | nil =>
      simp [depthsFromMoves, AdjacentDepthsDifferByOne]
  | cons move rest ih =>
      rcases hmoves with ⟨hmove, hrest⟩
      cases rest with
      | nil =>
          simp [depthsFromMoves, AdjacentDepthsDifferByOne]
          rcases hmove with hmove | hmove
          · exact Or.inl hmove
          · right
            omega
      | cons next tail =>
          exact ⟨unitDepthMove_step start move hmove,
            ih (start + move) hrest⟩

theorem depthsFromMoves_length (start : Int) (moves : List Int) :
    (depthsFromMoves start moves).length = moves.length + 1 := by
  induction moves generalizing start with
  | nil =>
      simp [depthsFromMoves]
  | cons move rest ih =>
      simp [depthsFromMoves, ih (start + move)]

mutual
  theorem RoseTree.eulerNodes_length_eq_moves (tree : RoseTree) :
      tree.eulerNodes.length = tree.eulerMoves.length + 1 := by
    cases tree with
    | node label children =>
        have hforest := RoseTree.eulerNodesForest_length_eq_moves label children
        simp [RoseTree.eulerNodes, RoseTree.eulerMoves, hforest]

  theorem RoseTree.eulerNodesForest_length_eq_moves
      (parent : Nat) (forest : List RoseTree) :
      (RoseTree.eulerNodesForest parent forest).length =
        (RoseTree.eulerMovesForest forest).length := by
    cases forest with
    | nil =>
        simp [RoseTree.eulerNodesForest, RoseTree.eulerMovesForest]
    | cons child rest =>
        have hchild := RoseTree.eulerNodes_length_eq_moves child
        have hrest := RoseTree.eulerNodesForest_length_eq_moves parent rest
        simp [RoseTree.eulerNodesForest, RoseTree.eulerMovesForest, hchild, hrest]
        omega
end

mutual
  theorem RoseTree.depthAfterMoves_eulerMoves
      (tree : RoseTree) (startDepth : Int) :
      depthAfterMoves startDepth tree.eulerMoves = startDepth := by
    cases tree with
    | node _ children =>
        simpa [RoseTree.eulerMoves] using
          RoseTree.depthAfterMoves_eulerMovesForest children startDepth

  theorem RoseTree.depthAfterMoves_eulerMovesForest
      (forest : List RoseTree) (startDepth : Int) :
      depthAfterMoves startDepth (RoseTree.eulerMovesForest forest) =
        startDepth := by
    cases forest with
    | nil =>
        simp [RoseTree.eulerMovesForest, depthAfterMoves]
    | cons child rest =>
        have hchild :
            depthAfterMoves (startDepth + 1) child.eulerMoves =
              startDepth + 1 :=
          RoseTree.depthAfterMoves_eulerMoves child (startDepth + 1)
        have hrest :
            depthAfterMoves startDepth (RoseTree.eulerMovesForest rest) =
              startDepth :=
          RoseTree.depthAfterMoves_eulerMovesForest rest startDepth
        simp [RoseTree.eulerMovesForest, depthAfterMoves, depthAfterMoves_append,
          hchild]
        have hstart : startDepth + 1 + -1 = startDepth := by
          omega
        simpa [hstart] using hrest
end

/-- Euler-tour depths for a tree rooted at `startDepth`. -/
def RoseTree.eulerDepthsAt (startDepth : Int) (tree : RoseTree) : List Int :=
  depthsFromMoves startDepth tree.eulerMoves

/-- Public Euler-tour depths, rooted at depth zero. -/
def RoseTree.eulerDepths (tree : RoseTree) : List Int :=
  tree.eulerDepthsAt 0

theorem RoseTree.eulerDepthsAt_adjacent
    (tree : RoseTree) (startDepth : Int) :
    AdjacentDepthsDifferByOne (tree.eulerDepthsAt startDepth) := by
  exact depthsFromMoves_adjacent startDepth (roseTree_eulerMoves_unit tree)

theorem RoseTree.eulerDepths_adjacent (tree : RoseTree) :
    AdjacentDepthsDifferByOne tree.eulerDepths := by
  exact tree.eulerDepthsAt_adjacent 0

namespace RoseTree

mutual
  /-- First root-to-label path in the tree, if the label is present. -/
  def pathTo? (target : Nat) : RoseTree -> Option (List Nat)
    | node label children =>
        if label = target then
          some [label]
        else
          match pathToForest? target children with
          | some path => some (label :: path)
          | none => none

  /-- First root-to-label path in a forest, if the label is present. -/
  def pathToForest? (target : Nat) : List RoseTree -> Option (List Nat)
    | [] => none
    | child :: rest =>
        match pathTo? target child with
        | some path => some path
        | none => pathToForest? target rest
end

mutual
  /-- Preorder list of labels in a tree. -/
  def labelsPreorder : RoseTree -> List Nat
    | node label children => label :: labelsPreorderForest children

  /-- Preorder list of labels in a forest. -/
  def labelsPreorderForest : List RoseTree -> List Nat
    | [] => []
    | child :: rest => labelsPreorder child ++ labelsPreorderForest rest
end

/--
Labels are intended to act as node identities for the label-path semantics.
Without this side condition, two different tree nodes with the same label can
make a label common-prefix path disagree with the Euler first-occurrence path.
-/
def LabelsUnique (tree : RoseTree) : Prop :=
  tree.labelsPreorder.Nodup

/--
Every label in the tree is a valid direct-address index into a table of size
`labelsPreorder.length`.  This is the cost-model assumption used by dense-node
LCA structures; it is intentionally separate from uniqueness.
-/
def LabelsBoundedBySize (tree : RoseTree) : Prop :=
  forall label, label ∈ tree.labelsPreorder -> label < tree.labelsPreorder.length

/--
Dense natural-number node labels: labels are unique semantic node identifiers
and also fit in the direct-address range used by costed first-occurrence tables.
-/
def DenseNatLabels (tree : RoseTree) : Prop :=
  tree.LabelsUnique ∧ tree.LabelsBoundedBySize

mutual
  /--
  The dense node-ID table has one slot per syntactic tree node, and each such
  node appears at least once in the generated Euler tour.
  -/
  theorem labelsPreorder_length_le_eulerNodes_length
      (tree : RoseTree) :
      tree.labelsPreorder.length <= tree.eulerNodes.length := by
    cases tree with
    | node label children =>
        have hforest :=
          labelsPreorderForest_length_le_eulerNodesForest_length label children
        simp [labelsPreorder, eulerNodes]
        omega

  theorem labelsPreorderForest_length_le_eulerNodesForest_length
      (parent : Nat) (forest : List RoseTree) :
      (labelsPreorderForest forest).length <=
        (eulerNodesForest parent forest).length := by
    cases forest with
    | nil =>
        simp [labelsPreorderForest, eulerNodesForest]
    | cons child rest =>
        have hchild :=
          labelsPreorder_length_le_eulerNodes_length child
        have hrest :=
          labelsPreorderForest_length_le_eulerNodesForest_length parent rest
        simp [labelsPreorderForest, eulerNodesForest]
        omega
end

theorem nodup_append_not_mem_right {α : Type u} {x : α} {xs ys : List α}
    (h : (xs ++ ys).Nodup) (hx : x ∈ xs) :
    x ∉ ys := by
  induction xs with
  | nil =>
      simp at hx
  | cons head tail ih =>
      simp at h hx
      rcases h with ⟨hhead, htail⟩
      rcases hx with hx | hx
      · intro hy
        subst x
        exact hhead.2 hy
      · exact ih htail hx

theorem nodup_append_not_mem_left {α : Type u} {x : α} {xs ys : List α}
    (h : (xs ++ ys).Nodup) (hy : x ∈ ys) :
    x ∉ xs := by
  intro hx
  exact nodup_append_not_mem_right h hx hy

theorem labelsUnique_root_not_mem_children
    {root : Nat} {children : List RoseTree}
    (h : (RoseTree.node root children).LabelsUnique) :
    root ∉ labelsPreorderForest children := by
  unfold LabelsUnique at h
  simp [labelsPreorder] at h
  exact h.1

theorem labelsUnique_children_nodup
    {root : Nat} {children : List RoseTree}
    (h : (RoseTree.node root children).LabelsUnique) :
    (labelsPreorderForest children).Nodup := by
  unfold LabelsUnique at h
  simp [labelsPreorder] at h
  exact h.2

theorem labelsUnique_child_of_cons
    {root : Nat} {child : RoseTree} {rest : List RoseTree}
    (h : (RoseTree.node root (child :: rest)).LabelsUnique) :
    child.LabelsUnique := by
  unfold LabelsUnique at h ⊢
  simp [labelsPreorder, labelsPreorderForest] at h ⊢
  exact List.Nodup.sublist
    (List.sublist_append_left child.labelsPreorder (labelsPreorderForest rest)) h.2

theorem labelsUnique_root_rest_of_cons
    {root : Nat} {child : RoseTree} {rest : List RoseTree}
    (h : (RoseTree.node root (child :: rest)).LabelsUnique) :
    (RoseTree.node root rest).LabelsUnique := by
  unfold LabelsUnique at h ⊢
  simp [labelsPreorder, labelsPreorderForest] at h ⊢
  exact ⟨h.1.2, List.Nodup.sublist
    (List.sublist_append_right child.labelsPreorder (labelsPreorderForest rest)) h.2⟩

theorem labelsUnique_child_not_mem_rest
    {root label : Nat} {child : RoseTree} {rest : List RoseTree}
    (h : (RoseTree.node root (child :: rest)).LabelsUnique)
    (hmem : label ∈ child.labelsPreorder) :
    label ∉ labelsPreorderForest rest := by
  unfold LabelsUnique at h
  simp [labelsPreorder, labelsPreorderForest] at h
  exact nodup_append_not_mem_right h.2 hmem

theorem labelsUnique_rest_not_mem_child
    {root label : Nat} {child : RoseTree} {rest : List RoseTree}
    (h : (RoseTree.node root (child :: rest)).LabelsUnique)
    (hmem : label ∈ labelsPreorderForest rest) :
    label ∉ child.labelsPreorder := by
  unfold LabelsUnique at h
  simp [labelsPreorder, labelsPreorderForest] at h
  exact nodup_append_not_mem_left h.2 hmem

mutual
  theorem mem_labelsPreorder_of_mem_eulerNodes
      {tree : RoseTree} {label : Nat}
      (hmem : label ∈ tree.eulerNodes) :
      label ∈ tree.labelsPreorder := by
    cases tree with
    | node root children =>
        simp [eulerNodes, labelsPreorder] at hmem ⊢
        rcases hmem with hroot | hforest
        · exact Or.inl hroot
        · rcases mem_labelsPreorderForest_or_parent_of_mem_eulerNodesForest
            hforest with hparent | hchildren
          · exact Or.inl hparent
          · exact Or.inr hchildren

  theorem mem_labelsPreorderForest_or_parent_of_mem_eulerNodesForest
      {forest : List RoseTree} {parent label : Nat}
      (hmem : label ∈ eulerNodesForest parent forest) :
      label = parent ∨ label ∈ labelsPreorderForest forest := by
    cases forest with
    | nil =>
        simp [eulerNodesForest] at hmem
    | cons child rest =>
        simp [eulerNodesForest, labelsPreorderForest] at hmem ⊢
        rcases hmem with hchild | hparent | hrest
        · exact Or.inr (Or.inl (mem_labelsPreorder_of_mem_eulerNodes hchild))
        · exact Or.inl hparent
        · rcases mem_labelsPreorderForest_or_parent_of_mem_eulerNodesForest
            hrest with hparent' | hrest'
          · exact Or.inl hparent'
          · exact Or.inr (Or.inr hrest')
end

mutual
  theorem mem_eulerNodes_of_mem_labelsPreorder
      {tree : RoseTree} {label : Nat}
      (hmem : label ∈ tree.labelsPreorder) :
      label ∈ tree.eulerNodes := by
    cases tree with
    | node root children =>
        simp [labelsPreorder, eulerNodes] at hmem ⊢
        rcases hmem with hroot | hchildren
        · exact Or.inl hroot
        · exact Or.inr
            (mem_eulerNodesForest_of_mem_labelsPreorderForest
              (parent := root) hchildren)

  theorem mem_eulerNodesForest_of_mem_labelsPreorderForest
      {forest : List RoseTree} {parent label : Nat}
      (hmem : label ∈ labelsPreorderForest forest) :
      label ∈ eulerNodesForest parent forest := by
    cases forest with
    | nil =>
        simp [labelsPreorderForest] at hmem
    | cons child rest =>
        simp [labelsPreorderForest, eulerNodesForest] at hmem ⊢
        rcases hmem with hchild | hrest
        · exact Or.inl (mem_eulerNodes_of_mem_labelsPreorder hchild)
        · exact Or.inr (Or.inr
            (mem_eulerNodesForest_of_mem_labelsPreorderForest
              (parent := parent) hrest))
end

mutual
  /-- Euler-tour root paths for a tree, using `basePath` as the parent path. -/
  def eulerPathsAt (basePath : List Nat) : RoseTree -> List (List Nat)
    | node label children =>
        let here := basePath ++ [label]
        here :: eulerPathsForestAt here children

  /-- Euler-tour root paths for a forest, returning to `parentPath` between children. -/
  def eulerPathsForestAt
      (parentPath : List Nat) : List RoseTree -> List (List Nat)
    | [] => []
    | child :: rest =>
        eulerPathsAt parentPath child ++
          parentPath :: eulerPathsForestAt parentPath rest
end

/-- Euler-tour root paths for a generated tree trace. -/
def eulerPaths (tree : RoseTree) : List (List Nat) :=
  tree.eulerPathsAt []

theorem getLast?_append_singleton {α : Type u} (xs : List α) (x : α) :
    (xs ++ [x]).getLast? = some x := by
  exact List.getLast?_concat

/-- Depth associated with a generated root path. -/
def pathDepth (path : List Nat) : Int :=
  (path.length : Int) - 1

mutual
  theorem eulerPathsAt_length_eq_eulerNodes
      (basePath : List Nat) (tree : RoseTree) :
      (tree.eulerPathsAt basePath).length = tree.eulerNodes.length := by
    cases tree with
    | node label children =>
        have hforest :
            (eulerPathsForestAt (basePath ++ [label]) children).length =
              (eulerNodesForest label children).length :=
          eulerPathsForestAt_length_eq_eulerNodesForest
            (basePath ++ [label]) label children
        simp [eulerPathsAt, eulerNodes, hforest]

  theorem eulerPathsForestAt_length_eq_eulerNodesForest
      (parentPath : List Nat) (parent : Nat) (forest : List RoseTree) :
      (eulerPathsForestAt parentPath forest).length =
        (eulerNodesForest parent forest).length := by
    cases forest with
    | nil =>
        simp [eulerPathsForestAt, eulerNodesForest]
    | cons child rest =>
        have hchild :
            (child.eulerPathsAt parentPath).length = child.eulerNodes.length :=
          eulerPathsAt_length_eq_eulerNodes parentPath child
        have hrest :
            (eulerPathsForestAt parentPath rest).length =
              (eulerNodesForest parent rest).length :=
          eulerPathsForestAt_length_eq_eulerNodesForest parentPath parent rest
        simp [eulerPathsForestAt, eulerNodesForest, hchild, hrest]
end

theorem eulerPaths_length_eq_eulerNodes (tree : RoseTree) :
    tree.eulerPaths.length = tree.eulerNodes.length := by
  exact eulerPathsAt_length_eq_eulerNodes [] tree

mutual
  theorem eulerDepthsAt_eq_eulerPathsAt_map_pathDepth
      (basePath : List Nat) (tree : RoseTree) :
      tree.eulerDepthsAt (basePath.length : Int) =
        (tree.eulerPathsAt basePath).map pathDepth := by
    cases tree with
    | node label children =>
        have hforest :=
          eulerMovesForest_depths_eq_eulerPathsForestAt_map_pathDepth
            (basePath ++ [label]) children
        have hstart :
            ((basePath ++ [label]).length : Int) - 1 =
              (basePath.length : Int) := by
          simp
        have hforest' :
            depthsFromMoves (basePath.length : Int)
                (RoseTree.eulerMovesForest children) =
              ((basePath ++ [label]) ::
                eulerPathsForestAt (basePath ++ [label]) children).map
                  pathDepth := by
          simpa [hstart] using hforest
        simpa [RoseTree.eulerDepthsAt, RoseTree.eulerMoves, eulerPathsAt,
          pathDepth] using hforest'

  theorem eulerMovesForest_depths_eq_eulerPathsForestAt_map_pathDepth
      (parentPath : List Nat) (forest : List RoseTree) :
      depthsFromMoves ((parentPath.length : Int) - 1)
          (RoseTree.eulerMovesForest forest) =
        (parentPath :: eulerPathsForestAt parentPath forest).map pathDepth := by
    cases forest with
    | nil =>
        simp [RoseTree.eulerMovesForest, eulerPathsForestAt, depthsFromMoves,
          pathDepth]
    | cons child rest =>
        let parentDepth := (parentPath.length : Int) - 1
        have hchild :
            child.eulerDepthsAt (parentPath.length : Int) =
              (child.eulerPathsAt parentPath).map pathDepth :=
          eulerDepthsAt_eq_eulerPathsAt_map_pathDepth parentPath child
        have hrest :
            depthsFromMoves parentDepth (RoseTree.eulerMovesForest rest) =
              (parentPath :: eulerPathsForestAt parentPath rest).map pathDepth := by
          simpa [parentDepth] using
            eulerMovesForest_depths_eq_eulerPathsForestAt_map_pathDepth
              parentPath rest
        have hreturn :
            depthAfterMoves (parentPath.length : Int) child.eulerMoves =
              (parentPath.length : Int) :=
          RoseTree.depthAfterMoves_eulerMoves child (parentPath.length : Int)
        have hparent_start :
            parentDepth + 1 = (parentPath.length : Int) := by
          unfold parentDepth
          omega
        have hafter :
            depthAfterMoves (parentPath.length : Int) child.eulerMoves + -1 =
              parentDepth := by
          rw [hreturn]
          unfold parentDepth
          omega
        have hchildDepths :
            depthsFromMoves (parentPath.length : Int) child.eulerMoves =
              (child.eulerPathsAt parentPath).map pathDepth := by
          simpa [RoseTree.eulerDepthsAt] using hchild
        have hparentDepth : pathDepth parentPath = parentDepth := by
          simp [pathDepth, parentDepth]
        calc
          depthsFromMoves parentDepth
              (RoseTree.eulerMovesForest (child :: rest))
              =
            parentDepth ::
              depthsFromMoves (parentDepth + 1)
                (child.eulerMoves ++ (-1) :: RoseTree.eulerMovesForest rest) := by
              simp [RoseTree.eulerMovesForest, depthsFromMoves]
          _ =
            parentDepth ::
              (depthsFromMoves (parentPath.length : Int) child.eulerMoves ++
                depthsFromMoves parentDepth (RoseTree.eulerMovesForest rest)) := by
              rw [hparent_start, depthsFromMoves_append_cons, hafter]
          _ =
            parentDepth ::
              ((child.eulerPathsAt parentPath).map pathDepth ++
                (parentPath :: eulerPathsForestAt parentPath rest).map pathDepth) := by
              rw [hchildDepths, hrest]
          _ =
            (parentPath ::
              eulerPathsForestAt parentPath (child :: rest)).map pathDepth := by
              simp [eulerPathsForestAt, List.map_append, hparentDepth]
end

theorem eulerDepths_eq_eulerPaths_map_pathDepth (tree : RoseTree) :
    tree.eulerDepths = tree.eulerPaths.map pathDepth := by
  simpa [RoseTree.eulerDepths, eulerPaths] using
    eulerDepthsAt_eq_eulerPathsAt_map_pathDepth [] tree

mutual
  theorem eulerPathsAt_last?_eq_eulerNodes
      (basePath : List Nat) (tree : RoseTree) :
      (tree.eulerPathsAt basePath).map List.getLast? =
        tree.eulerNodes.map some := by
    cases tree with
    | node label children =>
        have hhere : (basePath ++ [label]).getLast? = some label :=
          getLast?_append_singleton basePath label
        have hforest :
            (eulerPathsForestAt (basePath ++ [label]) children).map List.getLast? =
              (eulerNodesForest label children).map some :=
          eulerPathsForestAt_last?_eq_eulerNodesForest
            (basePath ++ [label]) label hhere children
        simp [eulerPathsAt, eulerNodes, hhere, hforest]

  theorem eulerPathsForestAt_last?_eq_eulerNodesForest
      (parentPath : List Nat) (parent : Nat)
      (hparent : parentPath.getLast? = some parent)
      (forest : List RoseTree) :
      (eulerPathsForestAt parentPath forest).map List.getLast? =
        (eulerNodesForest parent forest).map some := by
    cases forest with
    | nil =>
        simp [eulerPathsForestAt, eulerNodesForest]
    | cons child rest =>
        have hchild :
            (child.eulerPathsAt parentPath).map List.getLast? =
              child.eulerNodes.map some :=
          eulerPathsAt_last?_eq_eulerNodes parentPath child
        have hrest :
            (eulerPathsForestAt parentPath rest).map List.getLast? =
              (eulerNodesForest parent rest).map some :=
          eulerPathsForestAt_last?_eq_eulerNodesForest
            parentPath parent hparent rest
        simp [eulerPathsForestAt, eulerNodesForest, hchild, hparent, hrest]
end

theorem eulerPaths_last?_eq_eulerNodes (tree : RoseTree) :
    tree.eulerPaths.map List.getLast? = tree.eulerNodes.map some := by
  exact eulerPathsAt_last?_eq_eulerNodes [] tree

mutual
  theorem pathTo?_mem_eulerPathsAt
      (tree : RoseTree) (basePath : List Nat)
      {target : Nat} {path : List Nat}
      (hpath : tree.pathTo? target = some path) :
      basePath ++ path ∈ eulerPathsAt basePath tree := by
    cases tree with
    | node label children =>
        unfold pathTo? at hpath
        by_cases hlabel : label = target
        · simp [hlabel] at hpath
          cases hpath
          simp [eulerPathsAt, hlabel]
        · simp [hlabel] at hpath
          cases hforest : pathToForest? target children with
          | none =>
              simp [hforest] at hpath
          | some childPath =>
              simp [hforest] at hpath
              cases hpath
              have hmem :
                  (basePath ++ [label]) ++ childPath ∈
                    eulerPathsForestAt (basePath ++ [label]) children :=
                pathToForest?_mem_eulerPathsForestAt
                  children (basePath ++ [label]) hforest
              change basePath ++ (label :: childPath) ∈
                (basePath ++ [label]) ::
                  eulerPathsForestAt (basePath ++ [label]) children
              simp only [List.mem_cons]
              right
              simpa [List.append_assoc] using hmem

  theorem pathToForest?_mem_eulerPathsForestAt
      (forest : List RoseTree) (basePath : List Nat)
      {target : Nat} {path : List Nat}
      (hpath : pathToForest? target forest = some path) :
      basePath ++ path ∈ eulerPathsForestAt basePath forest := by
    cases forest with
    | nil =>
        simp [pathToForest?] at hpath
    | cons child rest =>
        unfold pathToForest? at hpath
        match hchild : child.pathTo? target with
        | some _ =>
            simp [hchild] at hpath
            cases hpath
            have hmem :
                basePath ++ path ∈ eulerPathsAt basePath child :=
              pathTo?_mem_eulerPathsAt child basePath hchild
            simp [eulerPathsForestAt, hmem]
        | none =>
            simp [hchild] at hpath
            have hmem :
                basePath ++ path ∈ eulerPathsForestAt basePath rest :=
              pathToForest?_mem_eulerPathsForestAt rest basePath hpath
            simp [eulerPathsForestAt, hmem]
end

theorem pathTo?_mem_eulerPaths
    {tree : RoseTree} {target : Nat} {path : List Nat}
    (hpath : tree.pathTo? target = some path) :
    path ∈ tree.eulerPaths := by
  simpa [eulerPaths] using pathTo?_mem_eulerPathsAt tree [] hpath

mutual
  theorem basePath_prefix_of_mem_eulerPathsAt
      (tree : RoseTree) (basePath : List Nat)
      {path : List Nat}
      (hmem : path ∈ tree.eulerPathsAt basePath) :
      basePath <+: path := by
    cases tree with
    | node label children =>
        simp [eulerPathsAt] at hmem
        rcases hmem with hhere | hforest
        · subst path
          exact ⟨[label], rfl⟩
        · have hprefix :
              (basePath ++ [label]) <+: path :=
            basePath_prefix_of_mem_eulerPathsForestAt
              children (basePath ++ [label]) hforest
          rcases hprefix with ⟨suffix, hsuffix⟩
          refine ⟨label :: suffix, ?_⟩
          simpa [List.append_assoc] using hsuffix

  theorem basePath_prefix_of_mem_eulerPathsForestAt
      (forest : List RoseTree) (basePath : List Nat)
      {path : List Nat}
      (hmem : path ∈ eulerPathsForestAt basePath forest) :
      basePath <+: path := by
    cases forest with
    | nil =>
        simp [eulerPathsForestAt] at hmem
    | cons child rest =>
        simp [eulerPathsForestAt] at hmem
        rcases hmem with hchild | hparent | hrest
        · exact basePath_prefix_of_mem_eulerPathsAt child basePath hchild
        · subst path
          exact ⟨[], by simp⟩
        · exact basePath_prefix_of_mem_eulerPathsForestAt rest basePath hrest
end

theorem getElem?_length_of_append_singleton_prefix
    {base path : List Nat} {label : Nat}
    (hprefix : base ++ [label] <+: path) :
    path[base.length]? = some label := by
  rcases hprefix with ⟨suffix, rfl⟩
  simp

theorem here_prefix_of_mem_eulerPathsAt_node
    (basePath : List Nat) (label : Nat) (children : List RoseTree)
    {path : List Nat}
    (hmem : path ∈ (RoseTree.node label children).eulerPathsAt basePath) :
    basePath ++ [label] <+: path := by
  simp [eulerPathsAt] at hmem
  rcases hmem with hhere | hforest
  · subst path
    exact ⟨[], by simp⟩
  · exact basePath_prefix_of_mem_eulerPathsForestAt
      children (basePath ++ [label]) hforest

theorem first_extra_of_mem_eulerPathsAt_node
    (basePath : List Nat) (label : Nat) (children : List RoseTree)
    {path : List Nat}
    (hmem : path ∈ (RoseTree.node label children).eulerPathsAt basePath) :
    path[basePath.length]? = some label := by
  exact getElem?_length_of_append_singleton_prefix
    (here_prefix_of_mem_eulerPathsAt_node basePath label children hmem)

theorem first_extra_mem_labelsPreorderForest_of_mem_eulerPathsForestAt
    (forest : List RoseTree) (basePath : List Nat)
    {path : List Nat} {label : Nat}
    (hmem : path ∈ eulerPathsForestAt basePath forest)
    (hget : path[basePath.length]? = some label) :
    label ∈ labelsPreorderForest forest := by
  induction forest with
  | nil =>
      simp [eulerPathsForestAt] at hmem
  | cons child rest ih =>
      cases child with
      | node childLabel childChildren =>
          simp [eulerPathsForestAt, labelsPreorderForest] at hmem ⊢
          rcases hmem with hchild | hparent | hrest
          · left
            have hfirst :
                path[basePath.length]? = some childLabel :=
              first_extra_of_mem_eulerPathsAt_node
                basePath childLabel childChildren hchild
            rw [hfirst] at hget
            have hlabel_eq : label = childLabel :=
              (Option.some.inj hget).symm
            simp [labelsPreorder, hlabel_eq]
          · subst path
            simp at hget
          · right
            exact ih hrest

end RoseTree

/-- Common prefix of two root paths. -/
def commonPrefix : List Nat -> List Nat -> List Nat
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
      if x = y then
        x :: commonPrefix xs ys
      else
        []

theorem commonPrefix_prefix_left (xs ys : List Nat) :
    commonPrefix xs ys <+: xs := by
  induction xs generalizing ys with
  | nil =>
      simp [commonPrefix, List.IsPrefix]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [commonPrefix, List.IsPrefix]
      | cons y ys =>
          by_cases hxy : x = y
          · subst y
            cases ih ys with
            | intro suffix hsuffix =>
                apply Exists.intro suffix
                simp [commonPrefix, hsuffix]
          · apply Exists.intro (x :: xs)
            simp [commonPrefix, hxy]

theorem commonPrefix_prefix_right (xs ys : List Nat) :
    commonPrefix xs ys <+: ys := by
  induction xs generalizing ys with
  | nil =>
      simp [commonPrefix, List.IsPrefix]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [commonPrefix, List.IsPrefix]
      | cons y ys =>
          by_cases hxy : x = y
          · subst y
            cases ih ys with
            | intro suffix hsuffix =>
                apply Exists.intro suffix
                simp [commonPrefix, hsuffix]
          · apply Exists.intro (y :: ys)
            simp [commonPrefix, hxy]

theorem commonPrefix_eq_left_of_prefix
    {xs ys : List Nat} (hprefix : xs <+: ys) :
    commonPrefix xs ys = xs := by
  rcases hprefix with ⟨suffix, rfl⟩
  induction xs with
  | nil =>
      simp [commonPrefix]
  | cons x xs ih =>
      simp [commonPrefix, ih]

theorem commonPrefix_eq_right_of_prefix
    {xs ys : List Nat} (hprefix : ys <+: xs) :
    commonPrefix xs ys = ys := by
  rcases hprefix with ⟨suffix, rfl⟩
  induction ys with
  | nil =>
      cases suffix with
      | nil => simp [commonPrefix]
      | cons x xs => simp [commonPrefix]
  | cons y ys ih =>
      simp [commonPrefix, ih]

theorem commonPrefix_append_common
    (base xs ys : List Nat) :
    commonPrefix (base ++ xs) (base ++ ys) =
      base ++ commonPrefix xs ys := by
  induction base with
  | nil =>
      simp
  | cons head tail ih =>
      simp [commonPrefix, ih]

theorem commonPrefix_comm (xs ys : List Nat) :
    commonPrefix xs ys = commonPrefix ys xs := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [commonPrefix]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [commonPrefix]
      | cons y ys =>
          by_cases hxy : x = y
          · subst y
            simp [commonPrefix, ih]
          · have hyx : y ≠ x := by
              intro hyx
              exact hxy hyx.symm
            simp [commonPrefix, hxy, hyx]

theorem prefix_eq_of_prefix_of_length_le
    {xs ys : List Nat}
    (hprefix : xs <+: ys)
    (hlen : ys.length <= xs.length) :
    xs = ys := by
  rcases hprefix with ⟨suffix, rfl⟩
  have hsuffix : suffix = [] := by
    cases suffix with
    | nil => rfl
    | cons x xs =>
        simp at hlen
        have hfalse : False := by
          omega
        exact False.elim hfalse
  simp [hsuffix]

theorem prefix_commonPrefix_of_prefixes
    {pref xs ys : List Nat}
    (hpref_x : pref <+: xs)
    (hpref_y : pref <+: ys) :
    pref <+: commonPrefix xs ys := by
  induction pref generalizing xs ys with
  | nil =>
      exact ⟨commonPrefix xs ys, by simp⟩
  | cons p pref ih =>
      rcases hpref_x with ⟨sx, rfl⟩
      rcases hpref_y with ⟨sy, rfl⟩
      have htail :
          pref <+: commonPrefix (pref ++ sx) (pref ++ sy) :=
        ih ⟨sx, rfl⟩ ⟨sy, rfl⟩
      rcases htail with ⟨suffix, hsuffix⟩
      refine ⟨suffix, ?_⟩
      simp [commonPrefix, hsuffix]

theorem getElem?_of_prefix
    {xs ys : List Nat} (hprefix : xs <+: ys)
    {idx value : Nat}
    (hget : xs[idx]? = some value) :
    ys[idx]? = some value := by
  rcases hprefix with ⟨suffix, rfl⟩
  have hidx : idx < xs.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  simpa [List.getElem?_append, hidx] using hget

theorem eq_commonPrefix_of_prefixes_of_length_ge
    {pref xs ys : List Nat}
    (hpref_x : pref <+: xs)
    (hpref_y : pref <+: ys)
    (hlen : (commonPrefix xs ys).length <= pref.length) :
    pref = commonPrefix xs ys := by
  exact prefix_eq_of_prefix_of_length_le
    (prefix_commonPrefix_of_prefixes hpref_x hpref_y) hlen

namespace RoseTree

theorem commonPrefix_eq_parentPath_of_child_and_rightForest
    (parentPath : List Nat)
    (childLabel : Nat) (childChildren rest : List RoseTree)
    (hchild_not_rest : childLabel ∉ labelsPreorderForest rest)
    {i j : Nat} {pathChild pathRight : List Nat}
    (hchild :
      ((RoseTree.node childLabel childChildren).eulerPathsAt parentPath)[i]? =
        some pathChild)
    (hright :
      (parentPath :: eulerPathsForestAt parentPath rest)[j]? =
        some pathRight) :
    commonPrefix pathChild pathRight = parentPath := by
  have hchild_mem :
      pathChild ∈ (RoseTree.node childLabel childChildren).eulerPathsAt parentPath :=
    List.mem_of_getElem? hchild
  cases j with
  | zero =>
      simp at hright
      subst pathRight
      exact commonPrefix_eq_right_of_prefix
        (basePath_prefix_of_mem_eulerPathsAt
          (RoseTree.node childLabel childChildren) parentPath hchild_mem)
  | succ j =>
      simp at hright
      have hright_mem :
          pathRight ∈ eulerPathsForestAt parentPath rest :=
        List.mem_of_getElem? hright
      let cp := commonPrefix pathChild pathRight
      have hparent_child : parentPath <+: pathChild :=
        basePath_prefix_of_mem_eulerPathsAt
          (RoseTree.node childLabel childChildren) parentPath hchild_mem
      have hparent_right : parentPath <+: pathRight :=
        basePath_prefix_of_mem_eulerPathsForestAt rest parentPath hright_mem
      have hcp_prefix_child : cp <+: pathChild := by
        exact commonPrefix_prefix_left pathChild pathRight
      have hcp_prefix_right : cp <+: pathRight := by
        exact commonPrefix_prefix_right pathChild pathRight
      have hlen : cp.length <= parentPath.length := by
        by_cases hle : cp.length <= parentPath.length
        · exact hle
        have hlt : parentPath.length < cp.length := by omega
        let extra := cp[parentPath.length]'hlt
        have hcp_get : cp[parentPath.length]? = some extra := by
          simp [extra, hlt]
        have hchild_get :
            pathChild[parentPath.length]? = some extra :=
          getElem?_of_prefix hcp_prefix_child hcp_get
        have hright_get :
            pathRight[parentPath.length]? = some extra :=
          getElem?_of_prefix hcp_prefix_right hcp_get
        have hchild_first :
            pathChild[parentPath.length]? = some childLabel :=
          first_extra_of_mem_eulerPathsAt_node
            parentPath childLabel childChildren hchild_mem
        rw [hchild_first] at hchild_get
        have hextra_eq : extra = childLabel :=
          (Option.some.inj hchild_get).symm
        have hextra_rest :
            extra ∈ labelsPreorderForest rest :=
          first_extra_mem_labelsPreorderForest_of_mem_eulerPathsForestAt
            rest parentPath hright_mem hright_get
        exact False.elim
          (hchild_not_rest (by simpa [hextra_eq] using hextra_rest))
      have hparent_eq_cp :
          parentPath = cp :=
        eq_commonPrefix_of_prefixes_of_length_ge
          hparent_child hparent_right (by simpa [cp] using hlen)
      simpa [cp] using hparent_eq_cp.symm

end RoseTree

/-- Direct path-based LCA of two root paths. -/
def pathLCA? (pathU pathV : List Nat) : Option Nat :=
  (commonPrefix pathU pathV).getLast?

/-- A node is a common ancestor of two root paths when it ends a common prefix. -/
def PathCommonAncestor (pathU pathV : List Nat) (ancestor : Nat) : Prop :=
  Exists fun pref : List Nat =>
    pref <+: pathU /\ pref <+: pathV /\ pref.getLast? = some ancestor

/--
Path-level LCA: the ancestor is the final label in the maximal common prefix of
the two root paths.
-/
def IsPathLCAOfPaths (pathU pathV : List Nat) (ancestor : Nat) : Prop :=
  pathLCA? pathU pathV = some ancestor /\
    PathCommonAncestor pathU pathV ancestor

theorem pathLCA?_isPathLCAOfPaths
    {pathU pathV : List Nat} {ancestor : Nat}
    (h : pathLCA? pathU pathV = some ancestor) :
    IsPathLCAOfPaths pathU pathV ancestor := by
  refine ⟨h, ?_⟩
  exact ⟨commonPrefix pathU pathV,
    commonPrefix_prefix_left pathU pathV,
    commonPrefix_prefix_right pathU pathV,
    h⟩

namespace RoseTree

/-- Direct path-based LCA for two labels in a tree. -/
def pathLCA? (tree : RoseTree) (u v : Nat) : Option Nat :=
  match tree.pathTo? u, tree.pathTo? v with
  | some pathU, some pathV => RMQ.pathLCA? pathU pathV
  | _, _ => none

/-- Tree-level path LCA spec for first-match root paths. -/
def IsPathLCA (tree : RoseTree) (u v ancestor : Nat) : Prop :=
  exists pathU pathV,
    tree.pathTo? u = some pathU /\
      tree.pathTo? v = some pathV /\
      IsPathLCAOfPaths pathU pathV ancestor

theorem pathLCA?_isPathLCA
    {tree : RoseTree} {u v ancestor : Nat}
    (h : tree.pathLCA? u v = some ancestor) :
    tree.IsPathLCA u v ancestor := by
  unfold pathLCA? at h
  cases hu : tree.pathTo? u with
  | none =>
      simp [hu] at h
  | some pathU =>
      cases hv : tree.pathTo? v with
      | none =>
          simp [hu, hv] at h
      | some pathV =>
          simp [hu, hv] at h
          exact ⟨pathU, pathV, hu, hv, pathLCA?_isPathLCAOfPaths h⟩

theorem pathLCA?_eq_of_isPathLCA
    {tree : RoseTree} {u v ancestor : Nat}
    (h : tree.IsPathLCA u v ancestor) :
    tree.pathLCA? u v = some ancestor := by
  rcases h with ⟨pathU, pathV, hu, hv, hlca, _hcommon⟩
  unfold pathLCA?
  rw [hu, hv]
  exact hlca

mutual
  theorem pathTo?_mem_labelsPreorder
      {tree : RoseTree} {target : Nat} {path : List Nat}
      (hpath : tree.pathTo? target = some path) :
      target ∈ tree.labelsPreorder := by
    cases tree with
    | node label children =>
        unfold pathTo? at hpath
        by_cases hlabel : label = target
        · simp [hlabel] at hpath
          simp [labelsPreorder, hlabel]
        · simp [hlabel] at hpath
          cases hforest : pathToForest? target children with
          | none =>
              simp [hforest] at hpath
          | some childPath =>
              simp [hforest] at hpath
              have hmem :
                  target ∈ labelsPreorderForest children :=
                pathToForest?_mem_labelsPreorderForest hforest
              simp [labelsPreorder, hmem]

  theorem pathToForest?_mem_labelsPreorderForest
      {forest : List RoseTree} {target : Nat} {path : List Nat}
      (hpath : pathToForest? target forest = some path) :
      target ∈ labelsPreorderForest forest := by
    cases forest with
    | nil =>
        simp [pathToForest?] at hpath
    | cons child rest =>
        unfold pathToForest? at hpath
        match hchild : child.pathTo? target with
        | some _ =>
            simp [hchild] at hpath
            have hmem :
                target ∈ child.labelsPreorder :=
              pathTo?_mem_labelsPreorder hchild
            simp [labelsPreorderForest, hmem]
        | none =>
            simp [hchild] at hpath
            have hmem :
                target ∈ labelsPreorderForest rest :=
              pathToForest?_mem_labelsPreorderForest hpath
            simp [labelsPreorderForest, hmem]
end

theorem labels_mem_of_pathLCA?_some
    {tree : RoseTree} {u v ancestor : Nat}
    (hpath : tree.pathLCA? u v = some ancestor) :
    u ∈ tree.labelsPreorder ∧ v ∈ tree.labelsPreorder := by
  unfold pathLCA? at hpath
  cases hu : tree.pathTo? u with
  | none =>
      simp [hu] at hpath
  | some pathU =>
      cases hv : tree.pathTo? v with
      | none =>
          simp [hu, hv] at hpath
      | some pathV =>
          exact ⟨pathTo?_mem_labelsPreorder hu,
            pathTo?_mem_labelsPreorder hv⟩

mutual
  theorem pathTo?_getLast?
      {tree : RoseTree} {target : Nat} {path : List Nat}
      (hpath : tree.pathTo? target = some path) :
      path.getLast? = some target := by
    cases tree with
    | node label children =>
        unfold pathTo? at hpath
        by_cases hlabel : label = target
        · simp [hlabel] at hpath
          cases hpath
          simp
        · simp [hlabel] at hpath
          cases hforest : pathToForest? target children with
          | none =>
              simp [hforest] at hpath
          | some childPath =>
              simp [hforest] at hpath
              cases hpath
              have hlast :
                  childPath.getLast? = some target :=
                pathToForest?_getLast? hforest
              cases childPath with
              | nil =>
                  simp at hlast
              | cons childLabel childRest =>
                  simpa using hlast

  theorem pathToForest?_getLast?
      {forest : List RoseTree} {target : Nat} {path : List Nat}
      (hpath : pathToForest? target forest = some path) :
      path.getLast? = some target := by
    cases forest with
    | nil =>
        simp [pathToForest?] at hpath
    | cons child rest =>
        unfold pathToForest? at hpath
        match hchild : child.pathTo? target with
        | some _ =>
            simp [hchild] at hpath
            cases hpath
            exact pathTo?_getLast? hchild
        | none =>
            simp [hchild] at hpath
            exact pathToForest?_getLast? hpath
end

theorem isPathLCA_of_pathTo_prefixes_of_commonPrefix_length_le
    {tree : RoseTree} {u v ancestor : Nat}
    {pathU pathV pathAncestor : List Nat}
    (hu : tree.pathTo? u = some pathU)
    (hv : tree.pathTo? v = some pathV)
    (hancestor : tree.pathTo? ancestor = some pathAncestor)
    (hprefU : pathAncestor <+: pathU)
    (hprefV : pathAncestor <+: pathV)
    (hlen : (commonPrefix pathU pathV).length <= pathAncestor.length) :
    tree.IsPathLCA u v ancestor := by
  have hpath_eq :
      pathAncestor = commonPrefix pathU pathV :=
    eq_commonPrefix_of_prefixes_of_length_ge hprefU hprefV hlen
  have hlast :
      pathAncestor.getLast? = some ancestor :=
    pathTo?_getLast? hancestor
  apply pathLCA?_isPathLCA
  unfold pathLCA?
  rw [hu, hv]
  simpa [RMQ.pathLCA?, ← hpath_eq] using hlast

mutual
  theorem pathTo?_exists_of_mem_labelsPreorder
      {tree : RoseTree} {target : Nat}
      (hmem : target ∈ tree.labelsPreorder) :
      exists path, tree.pathTo? target = some path := by
    cases tree with
    | node label children =>
        by_cases hlabel : label = target
        · refine ⟨[label], ?_⟩
          simp [pathTo?, hlabel]
        · have hchildMem : target ∈ labelsPreorderForest children := by
            have htarget_label : target ≠ label := by
              intro htarget_label
              exact hlabel htarget_label.symm
            simpa [labelsPreorder, htarget_label] using hmem
          rcases pathToForest?_exists_of_mem_labelsPreorderForest hchildMem with
            ⟨path, hpath⟩
          refine ⟨label :: path, ?_⟩
          simp [pathTo?, hlabel, hpath]

  theorem pathToForest?_exists_of_mem_labelsPreorderForest
      {forest : List RoseTree} {target : Nat}
      (hmem : target ∈ labelsPreorderForest forest) :
      exists path, pathToForest? target forest = some path := by
    cases forest with
    | nil =>
        simp [labelsPreorderForest] at hmem
    | cons child rest =>
        simp [labelsPreorderForest] at hmem
        rcases hmem with hchildMem | hrestMem
        · rcases pathTo?_exists_of_mem_labelsPreorder hchildMem with
            ⟨path, hpath⟩
          refine ⟨path, ?_⟩
          simp [pathToForest?, hpath]
        · rcases pathToForest?_exists_of_mem_labelsPreorderForest hrestMem with
            ⟨path, hpath⟩
          unfold pathToForest?
          cases hchild : child.pathTo? target with
          | none =>
              refine ⟨path, ?_⟩
              simp [hpath]
          | some childPath =>
              refine ⟨childPath, ?_⟩
              simp
end

mutual
  theorem pathTo?_eq_of_mem_eulerPathsAt_unique
      (tree : RoseTree) (basePath : List Nat)
      (hunique : tree.LabelsUnique)
      {path : List Nat} {target : Nat}
      (hmem : path ∈ tree.eulerPathsAt basePath)
      (hlast : path.getLast? = some target) :
      exists localPath,
        tree.pathTo? target = some localPath ∧
          path = basePath ++ localPath := by
    cases tree with
    | node label children =>
        simp [eulerPathsAt] at hmem
        rcases hmem with hhere | hforest
        · subst path
          have htarget : target = label := by
            have hlast_label :
                (basePath ++ [label]).getLast? = some label :=
              getLast?_append_singleton basePath label
            rw [hlast_label] at hlast
            exact (Option.some.inj hlast).symm
          subst target
          refine ⟨[label], ?_, ?_⟩
          · simp [pathTo?]
          · simp
        · have hparent :
              (basePath ++ [label]).getLast? = some label :=
            getLast?_append_singleton basePath label
          have hforestNodup :
              (labelsPreorderForest children).Nodup :=
            labelsUnique_children_nodup hunique
          have hlabel_not :
              label ∉ labelsPreorderForest children :=
            labelsUnique_root_not_mem_children hunique
          rcases pathToForest?_eq_or_parent_of_mem_eulerPathsForestAt_unique
              children (basePath ++ [label]) label
              hparent hforestNodup hlabel_not hforest hlast with
            ⟨htarget, hpath⟩ | ⟨childPath, hchildPath, hpath⟩
          · subst target
            refine ⟨[label], ?_, ?_⟩
            · simp [pathTo?]
            · simpa using hpath
          · have htarget_mem :
                target ∈ labelsPreorderForest children :=
              pathToForest?_mem_labelsPreorderForest hchildPath
            have htarget_ne : label ≠ target := by
              intro hlabel_target
              subst target
              exact hlabel_not htarget_mem
            refine ⟨label :: childPath, ?_, ?_⟩
            · simp [pathTo?, htarget_ne, hchildPath]
            · rw [hpath]
              simp [List.append_assoc]

  theorem pathToForest?_eq_or_parent_of_mem_eulerPathsForestAt_unique
      (forest : List RoseTree) (parentPath : List Nat) (parent : Nat)
      (hparent : parentPath.getLast? = some parent)
      (hforestNodup : (labelsPreorderForest forest).Nodup)
      (hparent_not : parent ∉ labelsPreorderForest forest)
      {path : List Nat} {target : Nat}
      (hmem : path ∈ eulerPathsForestAt parentPath forest)
      (hlast : path.getLast? = some target) :
      (target = parent ∧ path = parentPath) ∨
        exists localPath,
          pathToForest? target forest = some localPath ∧
            path = parentPath ++ localPath := by
    cases forest with
    | nil =>
        simp [eulerPathsForestAt] at hmem
    | cons child rest =>
        simp [eulerPathsForestAt] at hmem
        have hchildUnique : child.LabelsUnique := by
          unfold LabelsUnique
          simp [labelsPreorderForest] at hforestNodup
          exact List.Nodup.sublist
            (List.sublist_append_left child.labelsPreorder
              (labelsPreorderForest rest)) hforestNodup
        have hrestNodup : (labelsPreorderForest rest).Nodup := by
          simp [labelsPreorderForest] at hforestNodup
          exact List.Nodup.sublist
            (List.sublist_append_right child.labelsPreorder
              (labelsPreorderForest rest)) hforestNodup
        have hparent_not_child : parent ∉ child.labelsPreorder := by
          intro hmem_child
          exact hparent_not (by simp [labelsPreorderForest, hmem_child])
        have hparent_not_rest : parent ∉ labelsPreorderForest rest := by
          intro hmem_rest
          exact hparent_not (by simp [labelsPreorderForest, hmem_rest])
        rcases hmem with hchildMem | hreturn | hrestMem
        · rcases pathTo?_eq_of_mem_eulerPathsAt_unique
            child parentPath hchildUnique hchildMem hlast with
            ⟨localPath, hlocal, hpath⟩
          right
          refine ⟨localPath, ?_, hpath⟩
          simp [pathToForest?, hlocal]
        · subst path
          left
          have htarget : target = parent := by
            rw [hparent] at hlast
            exact (Option.some.inj hlast).symm
          exact ⟨htarget, rfl⟩
        · rcases pathToForest?_eq_or_parent_of_mem_eulerPathsForestAt_unique
            rest parentPath parent hparent hrestNodup hparent_not_rest
            hrestMem hlast with
            ⟨htarget, hpath⟩ | ⟨localPath, hlocal, hpath⟩
          · left
            exact ⟨htarget, hpath⟩
          · have htarget_rest :
                target ∈ labelsPreorderForest rest :=
              pathToForest?_mem_labelsPreorderForest hlocal
            have htarget_not_child : target ∉ child.labelsPreorder := by
              simp [labelsPreorderForest] at hforestNodup
              exact nodup_append_not_mem_left hforestNodup htarget_rest
            have hchild_none : child.pathTo? target = none := by
              cases hchild : child.pathTo? target with
              | none => rfl
              | some childPath =>
                  have htarget_child :
                      target ∈ child.labelsPreorder :=
                    pathTo?_mem_labelsPreorder hchild
                  exact False.elim (htarget_not_child htarget_child)
            right
            refine ⟨localPath, ?_, hpath⟩
            simp [pathToForest?, hchild_none, hlocal]
end

theorem pathTo?_eq_of_mem_eulerPaths_unique
    {tree : RoseTree} (hunique : tree.LabelsUnique)
    {path : List Nat} {target : Nat}
    (hmem : path ∈ tree.eulerPaths)
    (hlast : path.getLast? = some target) :
    tree.pathTo? target = some path := by
  rcases pathTo?_eq_of_mem_eulerPathsAt_unique
    tree [] hunique hmem hlast with
    ⟨localPath, hlocal, hpath⟩
  simp at hpath
  subst path
  simpa using hlocal

end RoseTree

/-- Find the first index containing `target`. -/
def firstIndexOf? {α : Type u} [DecidableEq α] (target : α) : List α -> Option Nat
  | [] => none
  | x :: xs =>
      if x = target then
        some 0
      else
        match firstIndexOf? target xs with
        | none => none
        | some idx => some (idx + 1)

theorem firstIndexOf?_lt_length
    {α : Type u} [DecidableEq α] {target : α} :
    forall {xs : List α} {idx : Nat},
      firstIndexOf? target xs = some idx -> idx < xs.length
  | [], _, h => by
      simp [firstIndexOf?] at h
  | x :: xs, idx, h => by
      unfold firstIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp
      · simp [hx] at h
        cases htail : firstIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            have htail_lt :
                tailIdx < xs.length :=
              firstIndexOf?_lt_length (target := target) htail
            cases h
            simp
            omega

theorem firstIndexOf?_getElem?
    {α : Type u} [DecidableEq α] {target : α} :
    forall {xs : List α} {idx : Nat},
      firstIndexOf? target xs = some idx -> xs[idx]? = some target
  | [], _, h => by
      simp [firstIndexOf?] at h
  | x :: xs, idx, h => by
      unfold firstIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp [hx]
      · simp [hx] at h
        cases htail : firstIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            cases h
            have hget :
                xs[tailIdx]? = some target :=
              firstIndexOf?_getElem? (target := target) htail
            simpa using hget

theorem firstIndexOf?_mem
    {α : Type u} [DecidableEq α] {target : α}
    {xs : List α} {idx : Nat}
    (h : firstIndexOf? target xs = some idx) :
    target ∈ xs := by
  exact List.mem_of_getElem? (firstIndexOf?_getElem? h)

theorem firstIndexOf?_exists_of_mem
    {α : Type u} [DecidableEq α] {target : α} :
    forall {xs : List α}, target ∈ xs -> exists idx, firstIndexOf? target xs = some idx
  | [], hmem => by
      simp at hmem
  | x :: xs, hmem => by
      unfold firstIndexOf?
      by_cases hx : x = target
      · exact ⟨0, by simp [hx]⟩
      · have htarget_x : target ≠ x := by
          intro htarget_x
          exact hx htarget_x.symm
        simp [hx, htarget_x] at hmem ⊢
        rcases firstIndexOf?_exists_of_mem (target := target) hmem with
          ⟨idx, hidx⟩
        exact ⟨idx + 1, by simp [hidx]⟩

/--
An Euler trace pairs tour nodes with tour depths. The plus/minus-one invariant is kept as
data so later LCA proofs can consume traces independently of the tree generator.
-/
structure EulerTrace where
  nodes : List Nat
  depths : List Int
  length_eq : nodes.length = depths.length
  adjacent_depths : AdjacentDepthsDifferByOne depths

/--
An Euler trace paired with root-path annotations for every tour position. The
paths are kept separate from `EulerTrace` so RMQ backends can remain purely
depth/list based.
-/
structure EulerPathTrace where
  trace : EulerTrace
  paths : List (List Nat)
  length_eq : paths.length = trace.nodes.length
  last?_eq_nodes : paths.map List.getLast? = trace.nodes.map some

/-- The generated Euler trace for a rose tree rooted at `startDepth`. -/
def RoseTree.eulerTraceAt (startDepth : Int) (tree : RoseTree) : EulerTrace where
  nodes := tree.eulerNodes
  depths := tree.eulerDepthsAt startDepth
  length_eq := by
    simp [RoseTree.eulerDepthsAt, depthsFromMoves_length,
      RoseTree.eulerNodes_length_eq_moves]
  adjacent_depths := tree.eulerDepthsAt_adjacent startDepth

/-- The generated Euler trace for a rose tree rooted at depth zero. -/
def RoseTree.eulerTrace (tree : RoseTree) : EulerTrace :=
  tree.eulerTraceAt 0

/-- The generated Euler trace together with root-path annotations. -/
def RoseTree.eulerPathTrace (tree : RoseTree) : EulerPathTrace where
  trace := tree.eulerTrace
  paths := tree.eulerPaths
  length_eq := by
    simpa [RoseTree.eulerTrace, RoseTree.eulerTraceAt] using
      tree.eulerPaths_length_eq_eulerNodes
  last?_eq_nodes := by
    simpa [RoseTree.eulerTrace, RoseTree.eulerTraceAt] using
      tree.eulerPaths_last?_eq_eulerNodes

namespace EulerPathTrace

/--
A node lookup in a path-annotated trace can be lifted to the path at the same
tour position, whose final label is exactly that node.
-/
theorem pathAt?_of_nodeAt?
    (pathTrace : EulerPathTrace) {idx node : Nat}
    (hnode : pathTrace.trace.nodes[idx]? = some node) :
    exists path,
      pathTrace.paths[idx]? = some path /\
        path.getLast? = some node := by
  rcases List.getElem?_eq_some_iff.mp hnode with ⟨hidx_nodes, hget_node⟩
  have hidx_paths : idx < pathTrace.paths.length := by
    rw [pathTrace.length_eq]
    exact hidx_nodes
  let path := pathTrace.paths[idx]'hidx_paths
  have hpath : pathTrace.paths[idx]? = some path := by
    simp [path, hidx_paths]
  have hmap := congrArg (fun xs => xs[idx]?) pathTrace.last?_eq_nodes
  have hleft :
      (pathTrace.paths.map List.getLast?)[idx]? = some path.getLast? := by
    simp [List.getElem?_map, hpath]
  have hright :
      (pathTrace.trace.nodes.map some)[idx]? = some (some node) := by
    simp [List.getElem?_map, hnode]
  change (pathTrace.paths.map List.getLast?)[idx]? =
    (pathTrace.trace.nodes.map some)[idx]? at hmap
  rw [hleft, hright] at hmap
  exact ⟨path, hpath, Option.some.inj hmap⟩

end EulerPathTrace

namespace EulerTrace

/-- First occurrence of a node label in the Euler tour. -/
def firstOccurrence? (trace : EulerTrace) (node : Nat) : Option Nat :=
  firstIndexOf? node trace.nodes

/-- Closed-over-positions, half-open-as-a-list-window interval between two tour positions. -/
def occurrenceWindow (i j : Nat) : Nat × Nat :=
  (Nat.min i j, Nat.max i j + 1)

theorem occurrenceWindow_fst_le_left (i j : Nat) :
    (occurrenceWindow i j).1 <= i := by
  exact Nat.min_le_left i j

theorem occurrenceWindow_fst_le_right (i j : Nat) :
    (occurrenceWindow i j).1 <= j := by
  exact Nat.min_le_right i j

theorem occurrenceWindow_left_lt_snd (i j : Nat) :
    i < (occurrenceWindow i j).2 := by
  exact Nat.lt_succ_of_le (Nat.le_max_left i j)

theorem occurrenceWindow_right_lt_snd (i j : Nat) :
    j < (occurrenceWindow i j).2 := by
  exact Nat.lt_succ_of_le (Nat.le_max_right i j)

theorem occurrenceWindow_shift_fst
    {offset i j : Nat} (_hi : offset <= i) (_hj : offset <= j) :
    (occurrenceWindow (i - offset) (j - offset)).1 =
      (occurrenceWindow i j).1 - offset := by
  rcases Nat.le_total i j with hij | hji
  · have hsub : i - offset <= j - offset :=
      Nat.sub_le_sub_right hij offset
    simp [occurrenceWindow, Nat.min_eq_left hij, Nat.min_eq_left hsub]
  · have hsub : j - offset <= i - offset :=
      Nat.sub_le_sub_right hji offset
    simp [occurrenceWindow, Nat.min_eq_right hji, Nat.min_eq_right hsub]

theorem occurrenceWindow_shift_snd
    {offset i j : Nat} (hi : offset <= i) (hj : offset <= j) :
    (occurrenceWindow (i - offset) (j - offset)).2 =
      (occurrenceWindow i j).2 - offset := by
  rcases Nat.le_total i j with hij | hji
  · have hsub : i - offset <= j - offset :=
      Nat.sub_le_sub_right hij offset
    simp [occurrenceWindow, Nat.max_eq_right hij, Nat.max_eq_right hsub]
    omega
  · have hsub : j - offset <= i - offset :=
      Nat.sub_le_sub_right hji offset
    simp [occurrenceWindow, Nat.max_eq_left hji, Nat.max_eq_left hsub]
    omega

/--
Reference trace-side LCA candidate: scan the first-occurrence window and return
the node at the leftmost minimum-depth position.
-/
def leftmostMinNode? (trace : EulerTrace) (u v : Nat) : Option Nat :=
  match trace.firstOccurrence? u, trace.firstOccurrence? v with
  | some i, some j =>
      let window := occurrenceWindow i j
      trace.nodes[scanWindow trace.depths window.1 (window.2 - window.1)]?
  | _, _ => none

theorem occurrenceWindow_valid
    (trace : EulerTrace) {u v i j : Nat}
    (hu : trace.firstOccurrence? u = some i)
    (hv : trace.firstOccurrence? v = some j) :
    ValidRange trace.depths (occurrenceWindow i j).1 (occurrenceWindow i j).2 := by
  have hi_nodes : i < trace.nodes.length :=
    firstIndexOf?_lt_length (target := u) hu
  have hj_nodes : j < trace.nodes.length :=
    firstIndexOf?_lt_length (target := v) hv
  have hi_depths : i < trace.depths.length := by
    simpa [trace.length_eq] using hi_nodes
  have hj_depths : j < trace.depths.length := by
    simpa [trace.length_eq] using hj_nodes
  have hmax_depths : Nat.max i j < trace.depths.length :=
    Nat.max_lt.2 ⟨hi_depths, hj_depths⟩
  have hmin_le_max : Nat.min i j <= Nat.max i j :=
    Nat.le_trans (Nat.min_le_left i j) (Nat.le_max_left i j)
  unfold occurrenceWindow
  constructor
  · omega
  · omega

/-- Query an RMQ backend over a tour-depth window and return the tour node there. -/
def minDepthNodeInWindow
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) : Option Nat :=
  match RMQBackend.queryBuilt backend left right with
  | none => none
  | some idx => trace.nodes[idx]?

theorem minDepthNodeInWindow_valid_exact
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {left right : Nat}
    (hValid : ValidRange trace.depths left right) :
    exists idx node,
      minDepthNodeInWindow trace backend left right = some node /\
        trace.nodes[idx]? = some node /\
        LeftmostArgMin trace.depths left right idx := by
  let len := right - left
  have hlen : 0 < len := by
    unfold len
    omega
  have hbound : left + len <= trace.depths.length := by
    unfold len
    omega
  have hright : left + len = right := by
    unfold len
    omega
  have harg_scan := scanWindow_leftmost trace.depths left len hlen hbound
  let idx := scanWindow trace.depths left len
  have harg : LeftmostArgMin trace.depths left right idx := by
    simpa [idx, hright] using harg_scan
  have hquery :
      RMQBackend.queryBuilt backend left right = some idx :=
    backend.complete harg
  have hidx_depths : idx < trace.depths.length := by
    exact Nat.lt_of_lt_of_le harg.2.2.2.1 hValid.2
  have hidx_nodes : idx < trace.nodes.length := by
    rw [trace.length_eq]
    exact hidx_depths
  let node := trace.nodes[idx]'hidx_nodes
  have hnode : trace.nodes[idx]? = some node := by
    simp [node, hidx_nodes]
  refine ⟨idx, node, ?_, hnode, harg⟩
  unfold minDepthNodeInWindow
  rw [hquery]
  exact hnode

/--
The RMQ-backed LCA candidate: look up both first occurrences, query the minimum
depth over the inclusive tour-position span, and map the returned RMQ index back
to its tour node.
-/
def lcaCandidate
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) : Option Nat :=
  match trace.firstOccurrence? u, trace.firstOccurrence? v with
  | some i, some j =>
      let window := occurrenceWindow i j
      minDepthNodeInWindow trace backend window.1 window.2
  | _, _ => none

/-- Trace-level LCA reduction spec: the answer is the node at the leftmost
minimum depth in the first-occurrence window. -/
def IsLCAAnswer (trace : EulerTrace) (u v node : Nat) : Prop :=
  exists i j idx,
    trace.firstOccurrence? u = some i /\
      trace.firstOccurrence? v = some j /\
      trace.nodes[idx]? = some node /\
      LeftmostArgMin trace.depths
        (occurrenceWindow i j).1 (occurrenceWindow i j).2 idx

theorem leftmostMinNode?_eq_of_isLCAAnswer
    {trace : EulerTrace} {u v node : Nat}
    (hanswer : IsLCAAnswer trace u v node) :
    trace.leftmostMinNode? u v = some node := by
  rcases hanswer with ⟨i, j, idx, hu, hv, hnode, harg⟩
  let left := (occurrenceWindow i j).1
  let right := (occurrenceWindow i j).2
  let len := right - left
  have hValid : ValidRange trace.depths left right := by
    simpa [left, right] using trace.occurrenceWindow_valid hu hv
  have hlen : 0 < len := by
    unfold len
    omega
  have hbound : left + len <= trace.depths.length := by
    unfold len
    omega
  have hright : left + len = right := by
    unfold len
    omega
  have hscan :
      LeftmostArgMin trace.depths left right
        (scanWindow trace.depths left len) := by
    simpa [hright] using scanWindow_leftmost trace.depths left len hlen hbound
  have hidx :
      scanWindow trace.depths left len = idx :=
    leftmostArgMin_unique trace.depths left right
      (scanWindow trace.depths left len) idx hscan (by
        simpa [left, right] using harg)
  unfold leftmostMinNode?
  rw [hu, hv]
  simpa [left, right, len, hidx] using hnode

theorem isLCAAnswer_of_leftmostMinNode?_eq
    {trace : EulerTrace} {u v node : Nat}
    (hresult : trace.leftmostMinNode? u v = some node) :
    IsLCAAnswer trace u v node := by
  unfold leftmostMinNode? at hresult
  cases hu : trace.firstOccurrence? u with
  | none =>
      simp [hu] at hresult
  | some i =>
      cases hv : trace.firstOccurrence? v with
      | none =>
          simp [hu, hv] at hresult
      | some j =>
          let left := (occurrenceWindow i j).1
          let right := (occurrenceWindow i j).2
          let len := right - left
          have hValid : ValidRange trace.depths left right := by
            simpa [left, right] using trace.occurrenceWindow_valid hu hv
          have hlen : 0 < len := by
            unfold len
            omega
          have hbound : left + len <= trace.depths.length := by
            unfold len
            omega
          have hright : left + len = right := by
            unfold len
            omega
          have harg :
              LeftmostArgMin trace.depths left right
                (scanWindow trace.depths left len) := by
            simpa [hright] using
              scanWindow_leftmost trace.depths left len hlen hbound
          simp [hu, hv] at hresult
          refine ⟨i, j, scanWindow trace.depths left len, hu, hv, ?_, ?_⟩
          · simpa [left, right, len] using hresult
          · simpa [left, right] using harg

theorem lcaCandidate_valid_exact
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {u v i j : Nat}
    (hu : trace.firstOccurrence? u = some i)
    (hv : trace.firstOccurrence? v = some j) :
    exists idx node,
      lcaCandidate trace backend u v = some node /\
        trace.nodes[idx]? = some node /\
        LeftmostArgMin trace.depths
          (occurrenceWindow i j).1 (occurrenceWindow i j).2 idx := by
  have hValid := trace.occurrenceWindow_valid hu hv
  rcases minDepthNodeInWindow_valid_exact trace backend hValid with
    ⟨idx, node, hres, hnode, harg⟩
  refine ⟨idx, node, ?_, hnode, harg⟩
  unfold lcaCandidate
  rw [hu, hv]
  exact hres

theorem lcaCandidate_isLCAAnswer
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {u v node : Nat}
    (hresult : lcaCandidate trace backend u v = some node) :
    IsLCAAnswer trace u v node := by
  unfold lcaCandidate at hresult
  cases hu : trace.firstOccurrence? u with
  | none =>
      simp [hu] at hresult
  | some i =>
      cases hv : trace.firstOccurrence? v with
      | none =>
          simp [hu, hv] at hresult
      | some j =>
          rcases lcaCandidate_valid_exact trace backend hu hv with
            ⟨idx, node', hcandidate, hnode, harg⟩
          unfold lcaCandidate at hcandidate
          simp [hu, hv] at hcandidate
          simp [hu, hv] at hresult
          have hnode_eq : node' = node := by
            have hsome : some node' = some node := by
              rw [← hcandidate, hresult]
            exact Option.some.inj hsome
          refine ⟨i, j, idx, hu, hv, ?_, ?_⟩
          · simpa [hnode_eq] using hnode
          · exact harg

end EulerTrace

namespace RoseTree

/-- Run the LCA reduction on the generated Euler trace of a tree. -/
def lcaCandidate
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    (u v : Nat) : Option Nat :=
  tree.eulerTrace.lcaCandidate backend u v

theorem lcaCandidate_valid_exact
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    exists idx node,
      tree.lcaCandidate backend u v = some node /\
        tree.eulerTrace.nodes[idx]? = some node /\
        LeftmostArgMin tree.eulerTrace.depths
          (EulerTrace.occurrenceWindow i j).1
          (EulerTrace.occurrenceWindow i j).2 idx := by
  exact EulerTrace.lcaCandidate_valid_exact tree.eulerTrace backend hu hv

theorem lcaCandidate_isLCAAnswer
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    {u v node : Nat}
    (hresult : tree.lcaCandidate backend u v = some node) :
    EulerTrace.IsLCAAnswer tree.eulerTrace u v node := by
  exact EulerTrace.lcaCandidate_isLCAAnswer tree.eulerTrace backend hresult

theorem eulerPathAt?_of_eulerTraceNodeAt?
    {tree : RoseTree} {idx node : Nat}
    (hnode : tree.eulerTrace.nodes[idx]? = some node) :
    exists path,
      tree.eulerPaths[idx]? = some path /\
        path.getLast? = some node := by
  simpa [eulerPathTrace] using
    (EulerPathTrace.pathAt?_of_nodeAt? tree.eulerPathTrace hnode)

/--
Every trace-level LCA answer for a generated trace has a generated root-path
witness at the selected Euler-tour position.
-/
theorem pathWitness_of_isLCAAnswer
    {tree : RoseTree} {u v node : Nat}
    (hanswer : EulerTrace.IsLCAAnswer tree.eulerTrace u v node) :
    exists i j idx path,
      tree.eulerTrace.firstOccurrence? u = some i /\
        tree.eulerTrace.firstOccurrence? v = some j /\
        tree.eulerPaths[idx]? = some path /\
        path.getLast? = some node /\
        LeftmostArgMin tree.eulerTrace.depths
          (EulerTrace.occurrenceWindow i j).1
          (EulerTrace.occurrenceWindow i j).2 idx := by
  rcases hanswer with ⟨i, j, idx, hu, hv, hnode, harg⟩
  rcases eulerPathAt?_of_eulerTraceNodeAt? hnode with
    ⟨path, hpath, hlast⟩
  exact ⟨i, j, idx, path, hu, hv, hpath, hlast, harg⟩

theorem pathWitness_pathTo_of_isLCAAnswer_unique
    {tree : RoseTree} (hunique : tree.LabelsUnique)
    {u v node : Nat}
    (hanswer : EulerTrace.IsLCAAnswer tree.eulerTrace u v node) :
    exists i j idx path,
      tree.eulerTrace.firstOccurrence? u = some i ∧
        tree.eulerTrace.firstOccurrence? v = some j ∧
        tree.eulerPaths[idx]? = some path ∧
        tree.pathTo? node = some path ∧
        LeftmostArgMin tree.eulerTrace.depths
          (EulerTrace.occurrenceWindow i j).1
          (EulerTrace.occurrenceWindow i j).2 idx := by
  rcases pathWitness_of_isLCAAnswer hanswer with
    ⟨i, j, idx, path, hu, hv, hpath, hlast, harg⟩
  have hmem : path ∈ tree.eulerPaths :=
    List.mem_of_getElem? hpath
  have hpathTo :
      tree.pathTo? node = some path :=
    pathTo?_eq_of_mem_eulerPaths_unique hunique hmem hlast
  exact ⟨i, j, idx, path, hu, hv, hpath, hpathTo, harg⟩

theorem pathAtFirstOccurrence?_pathTo_unique
    {tree : RoseTree} (hunique : tree.LabelsUnique)
    {label idx : Nat}
    (hfirst : tree.eulerTrace.firstOccurrence? label = some idx) :
    exists path,
      tree.eulerPaths[idx]? = some path ∧
        tree.pathTo? label = some path := by
  have hnode :
      tree.eulerTrace.nodes[idx]? = some label :=
    firstIndexOf?_getElem? hfirst
  rcases eulerPathAt?_of_eulerTraceNodeAt? hnode with
    ⟨path, hpath, hlast⟩
  have hmem : path ∈ tree.eulerPaths :=
    List.mem_of_getElem? hpath
  have hpathTo :
      tree.pathTo? label = some path :=
    pathTo?_eq_of_mem_eulerPaths_unique hunique hmem hlast
  exact ⟨path, hpath, hpathTo⟩

theorem pathWitness_with_endpoints_of_isLCAAnswer_unique
    {tree : RoseTree} (hunique : tree.LabelsUnique)
    {u v node : Nat}
    (hanswer : EulerTrace.IsLCAAnswer tree.eulerTrace u v node) :
    exists i j idx pathU pathV pathNode,
      tree.eulerTrace.firstOccurrence? u = some i ∧
        tree.eulerTrace.firstOccurrence? v = some j ∧
        tree.eulerPaths[i]? = some pathU ∧
        tree.eulerPaths[j]? = some pathV ∧
        tree.eulerPaths[idx]? = some pathNode ∧
        tree.pathTo? u = some pathU ∧
        tree.pathTo? v = some pathV ∧
        tree.pathTo? node = some pathNode ∧
        LeftmostArgMin tree.eulerTrace.depths
          (EulerTrace.occurrenceWindow i j).1
          (EulerTrace.occurrenceWindow i j).2 idx := by
  rcases pathWitness_pathTo_of_isLCAAnswer_unique hunique hanswer with
    ⟨i, j, idx, pathNode, hu, hv, hpathNode, hpathToNode, harg⟩
  rcases pathAtFirstOccurrence?_pathTo_unique hunique hu with
    ⟨pathU, hpathU, hpathToU⟩
  rcases pathAtFirstOccurrence?_pathTo_unique hunique hv with
    ⟨pathV, hpathV, hpathToV⟩
  exact ⟨i, j, idx, pathU, pathV, pathNode,
    hu, hv, hpathU, hpathV, hpathNode,
    hpathToU, hpathToV, hpathToNode, harg⟩

theorem firstOccurrence?_exists_of_mem_labelsPreorder
    {tree : RoseTree} {label : Nat}
    (hmem : label ∈ tree.labelsPreorder) :
    exists idx, tree.eulerTrace.firstOccurrence? label = some idx := by
  have hnodes : label ∈ tree.eulerTrace.nodes := by
    simpa [eulerTrace, eulerTraceAt] using
      (mem_eulerNodes_of_mem_labelsPreorder hmem)
  exact firstIndexOf?_exists_of_mem hnodes

theorem leftmostMinNode?_exists_of_mem_labelsPreorder
    {tree : RoseTree} {u v : Nat}
    (hu_mem : u ∈ tree.labelsPreorder)
    (hv_mem : v ∈ tree.labelsPreorder) :
    exists node, tree.eulerTrace.leftmostMinNode? u v = some node := by
  rcases firstOccurrence?_exists_of_mem_labelsPreorder hu_mem with ⟨i, hu⟩
  rcases firstOccurrence?_exists_of_mem_labelsPreorder hv_mem with ⟨j, hv⟩
  let left := (EulerTrace.occurrenceWindow i j).1
  let right := (EulerTrace.occurrenceWindow i j).2
  let len := right - left
  have hValid : ValidRange tree.eulerTrace.depths left right := by
    simpa [left, right] using tree.eulerTrace.occurrenceWindow_valid hu hv
  have hlen : 0 < len := by
    unfold len
    omega
  have hbound : left + len <= tree.eulerTrace.depths.length := by
    unfold len
    omega
  have hright : left + len = right := by
    unfold len
    omega
  have harg :
      LeftmostArgMin tree.eulerTrace.depths left right
        (scanWindow tree.eulerTrace.depths left len) := by
    simpa [hright] using
      scanWindow_leftmost tree.eulerTrace.depths left len hlen hbound
  have hidx_depths :
      scanWindow tree.eulerTrace.depths left len < tree.eulerTrace.depths.length := by
    exact Nat.lt_of_lt_of_le harg.2.2.2.1 hValid.2
  have hidx_nodes :
      scanWindow tree.eulerTrace.depths left len < tree.eulerTrace.nodes.length := by
    rw [tree.eulerTrace.length_eq]
    exact hidx_depths
  let node := tree.eulerTrace.nodes[scanWindow tree.eulerTrace.depths left len]'hidx_nodes
  have hnode :
      tree.eulerTrace.nodes[scanWindow tree.eulerTrace.depths left len]? = some node := by
    simp [node, hidx_nodes]
  refine ⟨node, ?_⟩
  unfold EulerTrace.leftmostMinNode?
  rw [hu, hv]
  simpa [left, right, len] using hnode

/--
Semantic agreement between generated Euler traces and direct root-path LCAs.
This is the remaining nontrivial tree theorem: every trace-level LCA answer for
the generated trace is also the direct common-prefix LCA of the root paths.
-/
def TracePathAgreement (tree : RoseTree) : Prop :=
  forall {u v node : Nat},
    EulerTrace.IsLCAAnswer tree.eulerTrace u v node ->
      tree.IsPathLCA u v node

/--
Pure generated-path window agreement: in any Euler window, the leftmost
minimum-depth path is exactly the common prefix of the endpoint paths.

This is the classical DFS/Euler-tour invariant needed to discharge
`TracePathAgreement` from structural uniqueness.
-/
def EulerPathWindowAgreement (tree : RoseTree) : Prop :=
  forall {i j idx : Nat} {pathI pathJ pathIdx : List Nat},
    tree.eulerPaths[i]? = some pathI ->
      tree.eulerPaths[j]? = some pathJ ->
        tree.eulerPaths[idx]? = some pathIdx ->
          LeftmostArgMin tree.eulerTrace.depths
            (EulerTrace.occurrenceWindow i j).1
            (EulerTrace.occurrenceWindow i j).2 idx ->
            pathIdx = commonPrefix pathI pathJ

/-- Every path inside a window extends the common prefix of the window endpoints. -/
def PathWindowPrefixInvariant (paths : List (List Nat)) : Prop :=
  forall {i j k : Nat} {pathI pathJ pathK : List Nat},
    paths[i]? = some pathI ->
      paths[j]? = some pathJ ->
        paths[k]? = some pathK ->
          (EulerTrace.occurrenceWindow i j).1 <= k ->
            k < (EulerTrace.occurrenceWindow i j).2 ->
              commonPrefix pathI pathJ <+: pathK

/--
Every generated path inside an Euler window extends the common prefix of the
window endpoints.
-/
def EulerPathWindowPrefixInvariant (tree : RoseTree) : Prop :=
  PathWindowPrefixInvariant tree.eulerPaths

/--
The common prefix of the endpoint paths is itself visited somewhere in the
corresponding Euler window.
-/
def PathWindowCommonPrefixWitness (paths : List (List Nat)) : Prop :=
  forall {i j : Nat} {pathI pathJ : List Nat},
    paths[i]? = some pathI ->
      paths[j]? = some pathJ ->
        exists k,
          (EulerTrace.occurrenceWindow i j).1 <= k /\
            k < (EulerTrace.occurrenceWindow i j).2 /\
              paths[k]? = some (commonPrefix pathI pathJ)

/--
The common prefix of the endpoint paths is itself visited somewhere in the
corresponding generated Euler window.
-/
def EulerPathWindowCommonPrefixWitness (tree : RoseTree) : Prop :=
  PathWindowCommonPrefixWitness tree.eulerPaths

theorem pathWindowPrefixInvariant_cons
    {base : List Nat} {paths : List (List Nat)}
    (htail : PathWindowPrefixInvariant paths)
    (hall : forall {k : Nat} {path : List Nat},
      paths[k]? = some path -> base <+: path) :
    PathWindowPrefixInvariant (base :: paths) := by
  intro i j k pathI pathJ pathK hpathI hpathJ hpathK hleft hright
  cases i with
  | zero =>
      simp at hpathI
      subst pathI
      cases j with
      | zero =>
          simp at hpathJ
          subst pathJ
          have hk_zero : k = 0 := by
            simp [EulerTrace.occurrenceWindow] at hright
            omega
          subst k
          simp at hpathK
          subst pathK
          exact commonPrefix_prefix_left base base
      | succ j =>
          simp at hpathJ
          have hbase_pathJ : base <+: pathJ := hall hpathJ
          have hcp : commonPrefix base pathJ = base :=
            commonPrefix_eq_left_of_prefix hbase_pathJ
          rw [hcp]
          cases k with
          | zero =>
              simp at hpathK
              subst pathK
              exact ⟨[], by simp⟩
          | succ k =>
              simp at hpathK
              exact hall hpathK
  | succ i =>
      simp at hpathI
      cases j with
      | zero =>
          simp at hpathJ
          subst pathJ
          have hbase_pathI : base <+: pathI := hall hpathI
          have hcp : commonPrefix pathI base = base :=
            commonPrefix_eq_right_of_prefix hbase_pathI
          rw [hcp]
          cases k with
          | zero =>
              simp at hpathK
              subst pathK
              exact ⟨[], by simp⟩
          | succ k =>
              simp at hpathK
              exact hall hpathK
      | succ j =>
          simp at hpathJ
          cases k with
          | zero =>
              simp [EulerTrace.occurrenceWindow] at hleft
          | succ k =>
              simp at hpathK
              exact htail hpathI hpathJ hpathK (by
                simp [EulerTrace.occurrenceWindow] at hleft ⊢
                omega) (by
                simp [EulerTrace.occurrenceWindow] at hright ⊢
                omega)

theorem pathWindowCommonPrefixWitness_cons
    {base : List Nat} {paths : List (List Nat)}
    (htail : PathWindowCommonPrefixWitness paths)
    (hall : forall {k : Nat} {path : List Nat},
      paths[k]? = some path -> base <+: path) :
    PathWindowCommonPrefixWitness (base :: paths) := by
  intro i j pathI pathJ hpathI hpathJ
  cases i with
  | zero =>
      simp at hpathI
      subst pathI
      cases j with
      | zero =>
          simp at hpathJ
          subst pathJ
          have hcp : commonPrefix base base = base :=
            commonPrefix_eq_left_of_prefix ⟨[], by simp⟩
          refine ⟨0, ?_, ?_, ?_⟩
          · simp [EulerTrace.occurrenceWindow]
          · simp [EulerTrace.occurrenceWindow]
          · simp [hcp]
      | succ j =>
          simp at hpathJ
          have hbase_pathJ : base <+: pathJ := hall hpathJ
          have hcp : commonPrefix base pathJ = base :=
            commonPrefix_eq_left_of_prefix hbase_pathJ
          refine ⟨0, ?_, ?_, ?_⟩
          · simp [EulerTrace.occurrenceWindow]
          · simp [EulerTrace.occurrenceWindow]
          · simp [hcp]
  | succ i =>
      simp at hpathI
      cases j with
      | zero =>
          simp at hpathJ
          subst pathJ
          have hbase_pathI : base <+: pathI := hall hpathI
          have hcp : commonPrefix pathI base = base :=
            commonPrefix_eq_right_of_prefix hbase_pathI
          refine ⟨0, ?_, ?_, ?_⟩
          · simp [EulerTrace.occurrenceWindow]
          · simp [EulerTrace.occurrenceWindow]
          · simp [hcp]
      | succ j =>
          simp at hpathJ
          rcases htail hpathI hpathJ with ⟨k, hleft, hright, hpath⟩
          refine ⟨k + 1, ?_, ?_, ?_⟩
          · simp [EulerTrace.occurrenceWindow] at hleft ⊢
            omega
          · simp [EulerTrace.occurrenceWindow] at hright ⊢
            omega
          · simpa using hpath

theorem pathWindowPrefixInvariant_append
    {base : List Nat} {leftPaths rightPaths : List (List Nat)}
    (hleft : PathWindowPrefixInvariant leftPaths)
    (hright : PathWindowPrefixInvariant rightPaths)
    (hallLeft : forall {k : Nat} {path : List Nat},
      leftPaths[k]? = some path -> base <+: path)
    (hallRight : forall {k : Nat} {path : List Nat},
      rightPaths[k]? = some path -> base <+: path)
    (hcross : forall {i j : Nat} {pathI pathJ : List Nat},
      leftPaths[i]? = some pathI ->
        rightPaths[j]? = some pathJ ->
          commonPrefix pathI pathJ = base) :
    PathWindowPrefixInvariant (leftPaths ++ rightPaths) := by
  intro i j k pathI pathJ pathK hpathI hpathJ hpathK hleft_k hright_k
  by_cases hi_left : i < leftPaths.length
  · have hpathI_left : leftPaths[i]? = some pathI := by
      simpa [List.getElem?_append, hi_left] using hpathI
    by_cases hj_left : j < leftPaths.length
    · have hpathJ_left : leftPaths[j]? = some pathJ := by
        simpa [List.getElem?_append, hj_left] using hpathJ
      have hk_left_lt : k < leftPaths.length := by
        have hmax_lt : Nat.max i j < leftPaths.length :=
          Nat.max_lt.2 ⟨hi_left, hj_left⟩
        simp [EulerTrace.occurrenceWindow] at hright_k
        omega
      have hpathK_left : leftPaths[k]? = some pathK := by
        simpa [List.getElem?_append, hk_left_lt] using hpathK
      exact hleft hpathI_left hpathJ_left hpathK_left hleft_k hright_k
    · have hj_ge : leftPaths.length <= j := by omega
      have hpathJ_right : rightPaths[j - leftPaths.length]? = some pathJ := by
        simpa [List.getElem?_append, hj_ge] using hpathJ
      have hcp : commonPrefix pathI pathJ = base :=
        hcross hpathI_left hpathJ_right
      rw [hcp]
      by_cases hk_left : k < leftPaths.length
      · have hpathK_left : leftPaths[k]? = some pathK := by
          simpa [List.getElem?_append, hk_left] using hpathK
        exact hallLeft hpathK_left
      · have hk_ge : leftPaths.length <= k := by omega
        have hpathK_right : rightPaths[k - leftPaths.length]? = some pathK := by
          simpa [List.getElem?_append, hk_ge] using hpathK
        exact hallRight hpathK_right
  · have hi_ge : leftPaths.length <= i := by omega
    have hpathI_right : rightPaths[i - leftPaths.length]? = some pathI := by
      simpa [List.getElem?_append, hi_ge] using hpathI
    by_cases hj_left : j < leftPaths.length
    · have hpathJ_left : leftPaths[j]? = some pathJ := by
        simpa [List.getElem?_append, hj_left] using hpathJ
      have hcp : commonPrefix pathI pathJ = base := by
        calc
          commonPrefix pathI pathJ = commonPrefix pathJ pathI := by
            exact commonPrefix_comm pathI pathJ
          _ = base := hcross hpathJ_left hpathI_right
      rw [hcp]
      by_cases hk_left : k < leftPaths.length
      · have hpathK_left : leftPaths[k]? = some pathK := by
          simpa [List.getElem?_append, hk_left] using hpathK
        exact hallLeft hpathK_left
      · have hk_ge : leftPaths.length <= k := by omega
        have hpathK_right : rightPaths[k - leftPaths.length]? = some pathK := by
          simpa [List.getElem?_append, hk_ge] using hpathK
        exact hallRight hpathK_right
    · have hj_ge : leftPaths.length <= j := by omega
      have hpathJ_right : rightPaths[j - leftPaths.length]? = some pathJ := by
        simpa [List.getElem?_append, hj_ge] using hpathJ
      have hk_ge : leftPaths.length <= k := by
        have hmin_ge : leftPaths.length <= Nat.min i j :=
          Nat.le_min.mpr ⟨hi_ge, hj_ge⟩
        simp [EulerTrace.occurrenceWindow] at hleft_k
        omega
      have hpathK_right : rightPaths[k - leftPaths.length]? = some pathK := by
        simpa [List.getElem?_append, hk_ge] using hpathK
      exact hright hpathI_right hpathJ_right hpathK_right (by
        rw [EulerTrace.occurrenceWindow_shift_fst hi_ge hj_ge]
        exact Nat.sub_le_sub_right hleft_k leftPaths.length) (by
        rw [EulerTrace.occurrenceWindow_shift_snd hi_ge hj_ge]
        omega)

theorem pathWindowCommonPrefixWitness_append
    {base : List Nat} {leftPaths rightPaths : List (List Nat)}
    (hleft : PathWindowCommonPrefixWitness leftPaths)
    (hright : PathWindowCommonPrefixWitness rightPaths)
    (hrightBase : rightPaths[0]? = some base)
    (hcross : forall {i j : Nat} {pathI pathJ : List Nat},
      leftPaths[i]? = some pathI ->
        rightPaths[j]? = some pathJ ->
          commonPrefix pathI pathJ = base) :
    PathWindowCommonPrefixWitness (leftPaths ++ rightPaths) := by
  intro i j pathI pathJ hpathI hpathJ
  by_cases hi_left : i < leftPaths.length
  · have hpathI_left : leftPaths[i]? = some pathI := by
      simpa [List.getElem?_append, hi_left] using hpathI
    by_cases hj_left : j < leftPaths.length
    · have hpathJ_left : leftPaths[j]? = some pathJ := by
        simpa [List.getElem?_append, hj_left] using hpathJ
      rcases hleft hpathI_left hpathJ_left with
        ⟨k, hk_left, hk_right, hpathK⟩
      have hk_len : k < leftPaths.length :=
        (List.getElem?_eq_some_iff.mp hpathK).1
      refine ⟨k, hk_left, hk_right, ?_⟩
      simpa [List.getElem?_append, hk_len] using hpathK
    · have hj_ge : leftPaths.length <= j := by omega
      have hpathJ_right : rightPaths[j - leftPaths.length]? = some pathJ := by
        simpa [List.getElem?_append, hj_ge] using hpathJ
      have hcp : commonPrefix pathI pathJ = base :=
        hcross hpathI_left hpathJ_right
      refine ⟨leftPaths.length, ?_, ?_, ?_⟩
      · have hij : i <= j := by omega
        simp [EulerTrace.occurrenceWindow, Nat.min_eq_left hij]
        omega
      · have hij : i <= j := by omega
        simp [EulerTrace.occurrenceWindow, Nat.max_eq_right hij]
        omega
      · rw [hcp]
        simpa [List.getElem?_append] using hrightBase
  · have hi_ge : leftPaths.length <= i := by omega
    have hpathI_right : rightPaths[i - leftPaths.length]? = some pathI := by
      simpa [List.getElem?_append, hi_ge] using hpathI
    by_cases hj_left : j < leftPaths.length
    · have hpathJ_left : leftPaths[j]? = some pathJ := by
        simpa [List.getElem?_append, hj_left] using hpathJ
      have hcp : commonPrefix pathI pathJ = base := by
        calc
          commonPrefix pathI pathJ = commonPrefix pathJ pathI := by
            exact commonPrefix_comm pathI pathJ
          _ = base := hcross hpathJ_left hpathI_right
      refine ⟨leftPaths.length, ?_, ?_, ?_⟩
      · have hji : j <= i := by omega
        simp [EulerTrace.occurrenceWindow, Nat.min_eq_right hji]
        omega
      · have hji : j <= i := by omega
        simp [EulerTrace.occurrenceWindow, Nat.max_eq_left hji]
        omega
      · rw [hcp]
        simpa [List.getElem?_append] using hrightBase
    · have hj_ge : leftPaths.length <= j := by omega
      have hpathJ_right : rightPaths[j - leftPaths.length]? = some pathJ := by
        simpa [List.getElem?_append, hj_ge] using hpathJ
      rcases hright hpathI_right hpathJ_right with
        ⟨k, hk_left, hk_right, hpathK⟩
      refine ⟨leftPaths.length + k, ?_, ?_, ?_⟩
      · have hmin_ge : leftPaths.length <= (EulerTrace.occurrenceWindow i j).1 := by
          have hmin_ge' : leftPaths.length <= Nat.min i j :=
            Nat.le_min.mpr ⟨hi_ge, hj_ge⟩
          simpa [EulerTrace.occurrenceWindow] using hmin_ge'
        rw [EulerTrace.occurrenceWindow_shift_fst hi_ge hj_ge] at hk_left
        omega
      · rw [EulerTrace.occurrenceWindow_shift_snd hi_ge hj_ge] at hk_right
        omega
      · have hge : leftPaths.length <= leftPaths.length + k := by omega
        simpa [List.getElem?_append, hge, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hpathK

mutual
  theorem pathWindowPrefixInvariant_eulerPathsAt
      (basePath : List Nat) (tree : RoseTree)
      (hunique : tree.LabelsUnique) :
      PathWindowPrefixInvariant (tree.eulerPathsAt basePath) := by
    cases tree with
    | node label children =>
        have hforest :
            PathWindowPrefixInvariant
              (eulerPathsForestAt (basePath ++ [label]) children) :=
          pathWindowPrefixInvariant_eulerPathsForestAt
            (basePath ++ [label]) children
            (labelsUnique_children_nodup hunique)
        have hall :
            forall {k : Nat} {path : List Nat},
              (eulerPathsForestAt (basePath ++ [label]) children)[k]? =
                some path ->
                  basePath ++ [label] <+: path := by
          intro k path hget
          exact basePath_prefix_of_mem_eulerPathsForestAt
            children (basePath ++ [label]) (List.mem_of_getElem? hget)
        unfold PathWindowPrefixInvariant
        intro i j k pathI pathJ pathK hpathI hpathJ hpathK hleft hright
        simpa [eulerPathsAt] using
          (pathWindowPrefixInvariant_cons hforest hall
            hpathI hpathJ hpathK hleft hright)

  theorem pathWindowPrefixInvariant_eulerPathsForestAt
      (parentPath : List Nat) (forest : List RoseTree)
      (hforestNodup : (labelsPreorderForest forest).Nodup) :
      PathWindowPrefixInvariant (eulerPathsForestAt parentPath forest) := by
    cases forest with
    | nil =>
        intro i j k pathI pathJ pathK hpathI _hpathJ _hpathK _hleft _hright
        simp [eulerPathsForestAt] at hpathI
    | cons child rest =>
        cases child with
        | node childLabel childChildren =>
            have hforestNodup' :
                ((RoseTree.node childLabel childChildren).labelsPreorder ++
                  labelsPreorderForest rest).Nodup := by
              simpa [labelsPreorderForest] using hforestNodup
            have hchildUnique :
                (RoseTree.node childLabel childChildren).LabelsUnique := by
              unfold LabelsUnique
              exact List.Nodup.sublist
                (List.sublist_append_left
                  (RoseTree.node childLabel childChildren).labelsPreorder
                  (labelsPreorderForest rest)) hforestNodup'
            have hrestNodup : (labelsPreorderForest rest).Nodup := by
              exact List.Nodup.sublist
                (List.sublist_append_right
                  (RoseTree.node childLabel childChildren).labelsPreorder
                  (labelsPreorderForest rest)) hforestNodup'
            have hchild_not_rest :
                childLabel ∉ labelsPreorderForest rest := by
              have hchildLabel_mem :
                  childLabel ∈
                    (RoseTree.node childLabel childChildren).labelsPreorder := by
                simp [labelsPreorder]
              exact nodup_append_not_mem_right hforestNodup' hchildLabel_mem
            have hchildInv :
                PathWindowPrefixInvariant
                  ((RoseTree.node childLabel childChildren).eulerPathsAt
                    parentPath) :=
              pathWindowPrefixInvariant_eulerPathsAt
                parentPath (RoseTree.node childLabel childChildren) hchildUnique
            have hrestInv :
                PathWindowPrefixInvariant
                  (eulerPathsForestAt parentPath rest) :=
              pathWindowPrefixInvariant_eulerPathsForestAt
                parentPath rest hrestNodup
            have hrestHall :
                forall {k : Nat} {path : List Nat},
                  (eulerPathsForestAt parentPath rest)[k]? = some path ->
                    parentPath <+: path := by
              intro k path hget
              exact basePath_prefix_of_mem_eulerPathsForestAt
                rest parentPath (List.mem_of_getElem? hget)
            have hrightInv :
                PathWindowPrefixInvariant
                  (parentPath :: eulerPathsForestAt parentPath rest) :=
              pathWindowPrefixInvariant_cons hrestInv hrestHall
            have hallLeft :
                forall {k : Nat} {path : List Nat},
                  ((RoseTree.node childLabel childChildren).eulerPathsAt
                    parentPath)[k]? = some path ->
                    parentPath <+: path := by
              intro k path hget
              exact basePath_prefix_of_mem_eulerPathsAt
                (RoseTree.node childLabel childChildren) parentPath
                (List.mem_of_getElem? hget)
            have hallRight :
                forall {k : Nat} {path : List Nat},
                  (parentPath :: eulerPathsForestAt parentPath rest)[k]? =
                    some path ->
                    parentPath <+: path := by
              intro k path hget
              cases k with
              | zero =>
                  simp at hget
                  subst path
                  exact ⟨[], by simp⟩
              | succ k =>
                  simp at hget
                  exact basePath_prefix_of_mem_eulerPathsForestAt
                    rest parentPath (List.mem_of_getElem? hget)
            have hcross :
                forall {i j : Nat} {pathI pathJ : List Nat},
                  ((RoseTree.node childLabel childChildren).eulerPathsAt
                    parentPath)[i]? = some pathI ->
                    (parentPath :: eulerPathsForestAt parentPath rest)[j]? =
                      some pathJ ->
                    commonPrefix pathI pathJ = parentPath := by
              intro i j pathI pathJ hpathI hpathJ
              exact commonPrefix_eq_parentPath_of_child_and_rightForest
                parentPath childLabel childChildren rest hchild_not_rest
                hpathI hpathJ
            unfold PathWindowPrefixInvariant
            intro i j k pathI pathJ pathK hpathI hpathJ hpathK hleft hright
            simpa [eulerPathsForestAt] using
              (pathWindowPrefixInvariant_append hchildInv hrightInv
                hallLeft hallRight hcross
                hpathI hpathJ hpathK hleft hright)
end

mutual
  theorem pathWindowCommonPrefixWitness_eulerPathsAt
      (basePath : List Nat) (tree : RoseTree)
      (hunique : tree.LabelsUnique) :
      PathWindowCommonPrefixWitness (tree.eulerPathsAt basePath) := by
    cases tree with
    | node label children =>
        have hforest :
            PathWindowCommonPrefixWitness
              (eulerPathsForestAt (basePath ++ [label]) children) :=
          pathWindowCommonPrefixWitness_eulerPathsForestAt
            (basePath ++ [label]) children
            (labelsUnique_children_nodup hunique)
        have hall :
            forall {k : Nat} {path : List Nat},
              (eulerPathsForestAt (basePath ++ [label]) children)[k]? =
                some path ->
                  basePath ++ [label] <+: path := by
          intro k path hget
          exact basePath_prefix_of_mem_eulerPathsForestAt
            children (basePath ++ [label]) (List.mem_of_getElem? hget)
        unfold PathWindowCommonPrefixWitness
        intro i j pathI pathJ hpathI hpathJ
        simpa [eulerPathsAt] using
          (pathWindowCommonPrefixWitness_cons hforest hall hpathI hpathJ)

  theorem pathWindowCommonPrefixWitness_eulerPathsForestAt
      (parentPath : List Nat) (forest : List RoseTree)
      (hforestNodup : (labelsPreorderForest forest).Nodup) :
      PathWindowCommonPrefixWitness (eulerPathsForestAt parentPath forest) := by
    cases forest with
    | nil =>
        intro i j pathI pathJ hpathI _hpathJ
        simp [eulerPathsForestAt] at hpathI
    | cons child rest =>
        cases child with
        | node childLabel childChildren =>
            have hforestNodup' :
                ((RoseTree.node childLabel childChildren).labelsPreorder ++
                  labelsPreorderForest rest).Nodup := by
              simpa [labelsPreorderForest] using hforestNodup
            have hchildUnique :
                (RoseTree.node childLabel childChildren).LabelsUnique := by
              unfold LabelsUnique
              exact List.Nodup.sublist
                (List.sublist_append_left
                  (RoseTree.node childLabel childChildren).labelsPreorder
                  (labelsPreorderForest rest)) hforestNodup'
            have hrestNodup : (labelsPreorderForest rest).Nodup := by
              exact List.Nodup.sublist
                (List.sublist_append_right
                  (RoseTree.node childLabel childChildren).labelsPreorder
                  (labelsPreorderForest rest)) hforestNodup'
            have hchild_not_rest :
                childLabel ∉ labelsPreorderForest rest := by
              have hchildLabel_mem :
                  childLabel ∈
                    (RoseTree.node childLabel childChildren).labelsPreorder := by
                simp [labelsPreorder]
              exact nodup_append_not_mem_right hforestNodup' hchildLabel_mem
            have hchildWitness :
                PathWindowCommonPrefixWitness
                  ((RoseTree.node childLabel childChildren).eulerPathsAt
                    parentPath) :=
              pathWindowCommonPrefixWitness_eulerPathsAt
                parentPath (RoseTree.node childLabel childChildren) hchildUnique
            have hrestWitness :
                PathWindowCommonPrefixWitness
                  (eulerPathsForestAt parentPath rest) :=
              pathWindowCommonPrefixWitness_eulerPathsForestAt
                parentPath rest hrestNodup
            have hrestHall :
                forall {k : Nat} {path : List Nat},
                  (eulerPathsForestAt parentPath rest)[k]? = some path ->
                    parentPath <+: path := by
              intro k path hget
              exact basePath_prefix_of_mem_eulerPathsForestAt
                rest parentPath (List.mem_of_getElem? hget)
            have hrightWitness :
                PathWindowCommonPrefixWitness
                  (parentPath :: eulerPathsForestAt parentPath rest) :=
              pathWindowCommonPrefixWitness_cons hrestWitness hrestHall
            have hrightBase :
                (parentPath :: eulerPathsForestAt parentPath rest)[0]? =
                  some parentPath := by
              simp
            have hcross :
                forall {i j : Nat} {pathI pathJ : List Nat},
                  ((RoseTree.node childLabel childChildren).eulerPathsAt
                    parentPath)[i]? = some pathI ->
                    (parentPath :: eulerPathsForestAt parentPath rest)[j]? =
                      some pathJ ->
                    commonPrefix pathI pathJ = parentPath := by
              intro i j pathI pathJ hpathI hpathJ
              exact commonPrefix_eq_parentPath_of_child_and_rightForest
                parentPath childLabel childChildren rest hchild_not_rest
                hpathI hpathJ
            unfold PathWindowCommonPrefixWitness
            intro i j pathI pathJ hpathI hpathJ
            simpa [eulerPathsForestAt] using
              (pathWindowCommonPrefixWitness_append
                hchildWitness hrightWitness hrightBase hcross
                hpathI hpathJ)
end

theorem eulerPathWindowAgreement_of_prefix_and_witness
    (tree : RoseTree)
    (hprefix : tree.EulerPathWindowPrefixInvariant)
    (hwitness : tree.EulerPathWindowCommonPrefixWitness) :
    tree.EulerPathWindowAgreement := by
  intro i j idx pathI pathJ pathIdx hpathI hpathJ hpathIdx harg
  let left := (EulerTrace.occurrenceWindow i j).1
  let right := (EulerTrace.occurrenceWindow i j).2
  let cp := commonPrefix pathI pathJ
  rcases harg with
    ⟨_hleft_right, _hright_len, hleft_idx, hidx_right,
      idxDepth, hidxDepth, hmin, _hleftmost⟩
  have hcp_prefix_idx : cp <+: pathIdx := by
    exact hprefix hpathI hpathJ hpathIdx hleft_idx hidx_right
  rcases hwitness hpathI hpathJ with
    ⟨cpIdx, hleft_cp, hcp_right, hcpPath⟩
  have hdepths :
      tree.eulerTrace.depths = tree.eulerPaths.map pathDepth := by
    simpa [RoseTree.eulerTrace, RoseTree.eulerTraceAt, RoseTree.eulerDepths] using
      eulerDepths_eq_eulerPaths_map_pathDepth tree
  have hidxDepthMap :
      (tree.eulerPaths.map pathDepth)[idx]? = some (pathDepth pathIdx) := by
    simp [List.getElem?_map, hpathIdx]
  have hcpDepthMap :
      (tree.eulerPaths.map pathDepth)[cpIdx]? = some (pathDepth cp) := by
    simp [cp, List.getElem?_map, hcpPath]
  have hidxDepthEq : idxDepth = pathDepth pathIdx := by
    rw [hdepths] at hidxDepth
    rw [hidxDepthMap] at hidxDepth
    exact (Option.some.inj hidxDepth).symm
  have hdepth_le : pathDepth pathIdx <= pathDepth cp := by
    have hmin_cp :
        idxDepth <= pathDepth cp := by
      exact hmin cpIdx (pathDepth cp) hleft_cp hcp_right (by
        rw [hdepths]
        exact hcpDepthMap)
    simpa [hidxDepthEq] using hmin_cp
  have hlen_le : pathIdx.length <= cp.length := by
    unfold pathDepth at hdepth_le
    omega
  have hcp_eq_idx : cp = pathIdx :=
    prefix_eq_of_prefix_of_length_le hcp_prefix_idx hlen_le
  exact hcp_eq_idx.symm

theorem tracePathAgreement_of_eulerPathWindowAgreement
    (tree : RoseTree)
    (hunique : tree.LabelsUnique)
    (hwindow : tree.EulerPathWindowAgreement) :
    tree.TracePathAgreement := by
  intro u v node hanswer
  rcases pathWitness_with_endpoints_of_isLCAAnswer_unique hunique hanswer with
    ⟨i, j, idx, pathU, pathV, pathNode,
      hu, hv, hpathU, hpathV, hpathNode,
      hpathToU, hpathToV, hpathToNode, harg⟩
  have hcommon :
      pathNode = commonPrefix pathU pathV :=
    hwindow hpathU hpathV hpathNode harg
  have hlast :
      pathNode.getLast? = some node :=
    pathTo?_getLast? hpathToNode
  apply pathLCA?_isPathLCA
  unfold pathLCA?
  rw [hpathToU, hpathToV]
  simpa [RMQ.pathLCA?, ← hcommon] using hlast

theorem tracePathAgreement_of_eulerPathWindowInvariants
    (tree : RoseTree)
    (hunique : tree.LabelsUnique)
    (hprefix : tree.EulerPathWindowPrefixInvariant)
    (hwitness : tree.EulerPathWindowCommonPrefixWitness) :
    tree.TracePathAgreement := by
  exact tree.tracePathAgreement_of_eulerPathWindowAgreement hunique
    (tree.eulerPathWindowAgreement_of_prefix_and_witness hprefix hwitness)

theorem eulerPathWindowPrefixInvariant_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    tree.EulerPathWindowPrefixInvariant := by
  unfold EulerPathWindowPrefixInvariant PathWindowPrefixInvariant
  intro i j k pathI pathJ pathK hpathI hpathJ hpathK hleft hright
  simpa [eulerPaths] using
    (pathWindowPrefixInvariant_eulerPathsAt [] tree hunique
      hpathI hpathJ hpathK hleft hright)

theorem eulerPathWindowCommonPrefixWitness_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    tree.EulerPathWindowCommonPrefixWitness := by
  unfold EulerPathWindowCommonPrefixWitness PathWindowCommonPrefixWitness
  intro i j pathI pathJ hpathI hpathJ
  simpa [eulerPaths] using
    (pathWindowCommonPrefixWitness_eulerPathsAt [] tree hunique
      hpathI hpathJ)

theorem eulerPathWindowAgreement_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    tree.EulerPathWindowAgreement := by
  exact tree.eulerPathWindowAgreement_of_prefix_and_witness
    (tree.eulerPathWindowPrefixInvariant_of_labelsUnique hunique)
    (tree.eulerPathWindowCommonPrefixWitness_of_labelsUnique hunique)

theorem tracePathAgreement_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    tree.TracePathAgreement := by
  exact tree.tracePathAgreement_of_eulerPathWindowAgreement hunique
    (tree.eulerPathWindowAgreement_of_labelsUnique hunique)

/--
Semantic exactness of the generated Euler reduction on labels that occur in the
tree. This is the proof-facing replacement for the finite boolean certificate:
for every real tree-label query, the trace-side reference answer agrees with
the direct common-prefix path LCA.
-/
def TracePathExactOnLabels (tree : RoseTree) : Prop :=
  forall {u v : Nat},
    u ∈ tree.labelsPreorder ->
      v ∈ tree.labelsPreorder ->
        tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v

theorem tracePathExactOnLabels_of_tracePathAgreement
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement) :
    tree.TracePathExactOnLabels := by
  intro u v hu_mem hv_mem
  rcases leftmostMinNode?_exists_of_mem_labelsPreorder hu_mem hv_mem with
    ⟨node, hleft⟩
  have hanswer :
      EulerTrace.IsLCAAnswer tree.eulerTrace u v node :=
    EulerTrace.isLCAAnswer_of_leftmostMinNode?_eq hleft
  have hpath :
      tree.pathLCA? u v = some node :=
    pathLCA?_eq_of_isPathLCA (hagreement hanswer)
  rw [hleft, hpath]

theorem tracePathAgreement_of_leftmostMinNode_eq_pathLCA
    (tree : RoseTree)
    (hagrees :
      forall u v, tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v) :
    tree.TracePathAgreement := by
  intro u v node hanswer
  apply pathLCA?_isPathLCA
  have hscan :
      tree.eulerTrace.leftmostMinNode? u v = some node :=
    EulerTrace.leftmostMinNode?_eq_of_isLCAAnswer hanswer
  have hpath := hagrees u v
  rw [← hpath]
  exact hscan

theorem tracePathAgreement_of_tracePathExactOnLabels
    (tree : RoseTree)
    (hexact : tree.TracePathExactOnLabels) :
    tree.TracePathAgreement := by
  intro u v node hanswer
  apply pathLCA?_isPathLCA
  rcases hanswer with ⟨i, j, idx, hu, hv, hnode, harg⟩
  have hleft :
      tree.eulerTrace.leftmostMinNode? u v = some node :=
    EulerTrace.leftmostMinNode?_eq_of_isLCAAnswer
      ⟨i, j, idx, hu, hv, hnode, harg⟩
  have hu_nodes : u ∈ tree.eulerTrace.nodes :=
    firstIndexOf?_mem hu
  have hv_nodes : v ∈ tree.eulerTrace.nodes :=
    firstIndexOf?_mem hv
  have hu_labels : u ∈ tree.labelsPreorder := by
    apply mem_labelsPreorder_of_mem_eulerNodes
    simpa [eulerTrace, eulerTraceAt] using hu_nodes
  have hv_labels : v ∈ tree.labelsPreorder := by
    apply mem_labelsPreorder_of_mem_eulerNodes
    simpa [eulerTrace, eulerTraceAt] using hv_nodes
  have hagree :
      tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v :=
    hexact hu_labels hv_labels
  rw [← hagree]
  exact hleft

/--
Finite generated-label certificate for the remaining trace/path agreement.
For every label that occurs in the tree, the trace-side reference answer must
match the direct path-LCA answer.
-/
def labelPairAgreement (tree : RoseTree) : Bool :=
  tree.labelsPreorder.all fun u =>
    tree.labelsPreorder.all fun v =>
      decide (tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v)

theorem tracePathExactOnLabels_of_labelPairAgreement
    (tree : RoseTree)
    (hcheck : tree.labelPairAgreement = true) :
    tree.TracePathExactOnLabels := by
  intro u v hu_labels hv_labels
  have hall_u :
      (tree.labelsPreorder.all fun v =>
        decide (tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v)) =
        true := by
    exact (List.all_eq_true.mp hcheck) u hu_labels
  have hagree_decide :
      decide (tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v) =
        true := by
    exact (List.all_eq_true.mp hall_u) v hv_labels
  have hagree :
      tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v := by
    exact of_decide_eq_true hagree_decide
  exact hagree

theorem tracePathAgreement_of_labelPairAgreement
    (tree : RoseTree)
    (hcheck : tree.labelPairAgreement = true) :
    tree.TracePathAgreement := by
  exact tree.tracePathAgreement_of_tracePathExactOnLabels
    (tree.tracePathExactOnLabels_of_labelPairAgreement hcheck)

theorem lcaCandidate_isPathLCA_of_tracePathAgreement
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    {u v node : Nat}
    (hresult : tree.lcaCandidate backend u v = some node) :
    tree.IsPathLCA u v node := by
  exact hagreement (tree.lcaCandidate_isLCAAnswer backend hresult)

theorem lcaCandidate_isPathLCA_of_tracePathExactOnLabels
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    (hexact : tree.TracePathExactOnLabels)
    {u v node : Nat}
    (hresult : tree.lcaCandidate backend u v = some node) :
    tree.IsPathLCA u v node := by
  exact lcaCandidate_isPathLCA_of_tracePathAgreement tree backend
    (tree.tracePathAgreement_of_tracePathExactOnLabels hexact) hresult

theorem lcaCandidate_isPathLCA_of_labelPairAgreement
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    (hcheck : tree.labelPairAgreement = true)
    {u v node : Nat}
    (hresult : tree.lcaCandidate backend u v = some node) :
    tree.IsPathLCA u v node := by
  exact lcaCandidate_isPathLCA_of_tracePathAgreement tree backend
    (tree.tracePathAgreement_of_labelPairAgreement hcheck) hresult

/--
Bridge from the RMQ-generated candidate to the path-level LCA spec, assuming
the trace candidate has been identified with the direct common-prefix path LCA.
The remaining tree-semantic theorem is precisely the proof of this agreement
for generated Euler traces.
-/
theorem lcaCandidate_isPathLCA_of_pathLCA
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    {u v node : Nat}
    (_hresult : tree.lcaCandidate backend u v = some node)
    (hpath : tree.pathLCA? u v = some node) :
    tree.IsPathLCA u v node := by
  exact pathLCA?_isPathLCA hpath

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).eulerTrace.nodes =
      [0, 1, 0, 2, 0] := by
  decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).eulerTrace.depths =
      [0, 1, 0, 1, 0] := by
  decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).pathTo? 2 =
      some [0, 2] := by
  decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).pathLCA? 1 2 =
      some 0 := by
  decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).labelPairAgreement =
      true := by
  decide

/--
A duplicate-label tree showing why the generated trace/path agreement needs
either unique node labels or an address-based path semantics.
-/
def duplicateLabelCounterexample : RoseTree :=
  RoseTree.node 0
    [RoseTree.node 1 [], RoseTree.node 1 [RoseTree.node 2 []]]

example : Not duplicateLabelCounterexample.LabelsUnique := by
  have hlabels :
      duplicateLabelCounterexample.labelsPreorder = [0, 1, 1, 2] := by
    decide
  unfold LabelsUnique
  rw [hlabels]
  simp

example : duplicateLabelCounterexample.eulerTrace.leftmostMinNode? 1 2 = some 0 := by
  decide

example : duplicateLabelCounterexample.pathLCA? 1 2 = some 1 := by
  decide

example : duplicateLabelCounterexample.labelPairAgreement = false := by
  decide

theorem duplicateLabelCounterexample_traceAnswer :
    EulerTrace.IsLCAAnswer duplicateLabelCounterexample.eulerTrace 1 2 0 := by
  refine ⟨1, 4, 2, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · have hdepths :
        duplicateLabelCounterexample.eulerTrace.depths =
          [0, 1, 0, 1, 2, 1, 0] := by
      decide
    simpa [EulerTrace.occurrenceWindow, hdepths] using
      (show LeftmostArgMin [0, 1, 0, 1, 2, 1, 0] 1 5 2 from by
        refine ⟨by omega, by decide, by omega, by omega, 0, by simp, ?_, ?_⟩
        · intro j w hj_left hj_right hget
          have hj_cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
            omega
          rcases hj_cases with rfl | rfl | rfl | rfl
          · simp at hget
            omega
          · simp at hget
            omega
          · simp at hget
            omega
          · simp at hget
            omega
        · intro j w hj_left hj_idx hget
          have hj : j = 1 := by
            omega
          subst j
          simp at hget
          omega)

theorem duplicateLabelCounterexample_not_tracePathAgreement :
    Not duplicateLabelCounterexample.TracePathAgreement := by
  intro hagreement
  have hpath :
      duplicateLabelCounterexample.IsPathLCA 1 2 0 :=
    hagreement duplicateLabelCounterexample_traceAnswer
  rcases hpath with ⟨pathU, pathV, hu, hv, hlca, _hcommon⟩
  have hpathU : duplicateLabelCounterexample.pathTo? 1 = some [0, 1] := by
    decide
  have hpathV : duplicateLabelCounterexample.pathTo? 2 = some [0, 1, 2] := by
    decide
  rw [hpathU] at hu
  rw [hpathV] at hv
  cases hu
  cases hv
  simp [RMQ.pathLCA?, commonPrefix] at hlca

end RoseTree

end RMQ

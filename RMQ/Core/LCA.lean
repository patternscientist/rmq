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
  native_decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).eulerTrace.depths =
      [0, 1, 0, 1, 0] := by
  native_decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).pathTo? 2 =
      some [0, 2] := by
  native_decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).pathLCA? 1 2 =
      some 0 := by
  native_decide

example :
    (RoseTree.node 0 [RoseTree.node 1 [], RoseTree.node 2 []]).labelPairAgreement =
      true := by
  native_decide

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
    native_decide
  unfold LabelsUnique
  rw [hlabels]
  simp

example : duplicateLabelCounterexample.eulerTrace.leftmostMinNode? 1 2 = some 0 := by
  native_decide

example : duplicateLabelCounterexample.pathLCA? 1 2 = some 1 := by
  native_decide

example : duplicateLabelCounterexample.labelPairAgreement = false := by
  native_decide

theorem duplicateLabelCounterexample_traceAnswer :
    EulerTrace.IsLCAAnswer duplicateLabelCounterexample.eulerTrace 1 2 0 := by
  refine ⟨1, 4, 2, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · have hdepths :
        duplicateLabelCounterexample.eulerTrace.depths =
          [0, 1, 0, 1, 2, 1, 0] := by
      native_decide
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
    native_decide
  have hpathV : duplicateLabelCounterexample.pathTo? 2 = some [0, 1, 2] := by
    native_decide
  rw [hpathU] at hu
  rw [hpathV] at hv
  cases hu
  cases hv
  simp [RMQ.pathLCA?, commonPrefix] at hlca

end RoseTree

end RMQ
